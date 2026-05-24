/*! bittorrent-protocol. MIT License. WebTorrent LLC <https://webtorrent.io/opensource> */
import bencode from 'bencode'
import BitField from 'bitfield'
import Debug from 'debug'
import { Duplex } from 'streamx'
import { concat, equal, hex2arr, arr2hex, text2arr, arr2text, randomBytes, hash } from 'uint8-util'
import throughput from 'throughput'
import arrayRemove from 'unordered-array-remove'
import { MessageStreamEncryptor, REQ1_STR, REQ3_STR, VC, xor } from './mse.js'

const debug = Debug('bittorrent-protocol')

const BITFIELD_GROW = 400000
const KEEP_ALIVE_TIMEOUT = 55000
const ALLOWED_FAST_SET_MAX_LENGTH = 100

const MESSAGE_PROTOCOL = text2arr('\u0013BitTorrent protocol')
const MESSAGE_KEEP_ALIVE = new Uint8Array([0x00, 0x00, 0x00, 0x00])
const MESSAGE_CHOKE = new Uint8Array([0x00, 0x00, 0x00, 0x01, 0x00])
const MESSAGE_UNCHOKE = new Uint8Array([0x00, 0x00, 0x00, 0x01, 0x01])
const MESSAGE_INTERESTED = new Uint8Array([0x00, 0x00, 0x00, 0x01, 0x02])
const MESSAGE_UNINTERESTED = new Uint8Array([0x00, 0x00, 0x00, 0x01, 0x03])

const MESSAGE_RESERVED = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
const MESSAGE_PORT = [0x00, 0x00, 0x00, 0x03, 0x09, 0x00, 0x00]

// BEP6 Fast Extension
const MESSAGE_HAVE_ALL = new Uint8Array([0x00, 0x00, 0x00, 0x01, 0x0E])
const MESSAGE_HAVE_NONE = new Uint8Array([0x00, 0x00, 0x00, 0x01, 0x0F])

const SYNC_MAX_BYTES = 512

/**
 * @param {Uint8Array} buffer
 * @param {number} at
 * @returns number
 */
function getUint32 (buffer, at = 0) {
  return (buffer[at] << 24) | (buffer[at + 1] << 16) | (buffer[at + 2] << 8) | buffer[at + 3]
}

/**
 * @param {Uint8Array} buffer
 * @param {number} at
 * @param {number} value
 */
function setUint32 (buffer, at, value) {
  buffer[at] = (value >>> 24) & 0xFF
  buffer[at + 1] = (value >>> 16) & 0xFF
  buffer[at + 2] = (value >>> 8) & 0xFF
  buffer[at + 3] = value & 0xFF
}

class Request {
  constructor (piece, offset, length, callback) {
    this.piece = piece
    this.offset = offset
    this.length = length
    this.callback = callback
  }
}

class HaveAllBitField {
  constructor () {
    this.buffer = new Uint8Array() // dummy
  }

  get (index) {
    return true
  }

  set (index) {}
}

class Wire extends Duplex {
  constructor (type = null, retries = 0, peEnabled = false) {
    super()

    this._debugId = arr2hex(randomBytes(4))
    this._debug('new wire')

    this.peerId = null // remote peer id (hex string)
    this.peerIdBuffer = null // remote peer id (buffer)
    this.type = type // connection type ('webrtc', 'tcpIncoming', 'tcpOutgoing', 'webSeed')

    this.amChoking = true // are we choking the peer?
    this.amInterested = false // are we interested in the peer?

    this.peerChoking = true // is the peer choking us?
    this.peerInterested = false // is the peer interested in us?

    // The largest torrent that I know of (the Geocities archive) is ~641 GB and has
    // ~41,000 pieces. Therefore, cap bitfield to 10x larger (400,000 bits) to support all
    // possible torrents but prevent malicious peers from growing bitfield to fill memory.
    this.peerPieces = new BitField(0, { grow: BITFIELD_GROW })

    this.extensions = {}
    this.peerExtensions = {}

    this.requests = [] // outgoing
    this.peerRequests = [] // incoming

    this.extendedMapping = {} // number -> string, ex: 1 -> 'ut_metadata'
    this.peerExtendedMapping = {} // string -> number, ex: 9 -> 'ut_metadata'

    // The extended handshake to send, minus the "m" field, which gets automatically
    // filled from `this.extendedMapping`
    this.extendedHandshake = {}

    this.peerExtendedHandshake = {} // remote peer's extended handshake

    // BEP6 Fast Estension
    this.hasFast = false // is fast extension enabled?
    this.allowedFastSet = [] // allowed fast set
    this.peerAllowedFastSet = [] // peer's allowed fast set

    this._ext = {} // string -> function, ex 'ut_metadata' -> ut_metadata()
    this._nextExt = 1

    this.uploaded = 0
    this.downloaded = 0
    this.uploadSpeed = throughput()
    this.downloadSpeed = throughput()

    this._keepAliveInterval = null
    this._timeout = null
    this._timeoutMs = 0
    this._timeoutExpiresAt = null

    this._finished = false

    this._parserSize = 0 // number of needed bytes to parse next message from remote peer
    this._parser = null // function to call once `this._parserSize` bytes are available

    this._buffer = [] // incomplete message data
    this._bufferSize = 0 // cached total length of buffers in `this._buffer`

    this._peEnabled = peEnabled
    this._peState = 'idle' // idle | sentPe1 | gotPe2 | sentPe3 | gotPe3 | done | fallback
    this._asyncParsePending = false
    this._encryptor = null
    this._infoHash = null
    this._cryptoHandshakeDone = false

    this._cryptoSyncPattern = null // the pattern to search for when resynchronizing after receiving pe1/pe2
    this._waitMaxBytes = null // the maximum number of bytes resynchronization must occur within
    this._encryptionMethod = null // 1 for plaintext, 2 for RC4

    this.on('finish', this._onFinish)
    this._debug('type:', this.type)

    if (this.type === 'tcpIncoming' && this._peEnabled) {
      // If we are not the initiator, we should wait to see if the client begins
      // with PE/MSE handshake or the standard bittorrent handshake.
      this._determineHandshakeType()
    } else if (this.type === 'tcpOutgoing' && this._peEnabled && retries === 0) {
      this._parsePe2()
    } else {
      this._parseHandshake(null)
    }
  }

  /**
   * Set whether to send a "keep-alive" ping (sent every 55s)
   * @param {boolean} enable
   */
  setKeepAlive (enable) {
    this._debug('setKeepAlive %s', enable)
    clearInterval(this._keepAliveInterval)
    if (enable === false) return
    this._keepAliveInterval = setInterval(() => {
      this.keepAlive()
    }, KEEP_ALIVE_TIMEOUT)
  }

  /**
   * Set the amount of time to wait before considering a request to be "timed out"
   * @param {number} ms
   * @param {boolean=} unref (should the timer be unref'd? default: false)
   */
  setTimeout (ms, unref) {
    this._debug('setTimeout ms=%d unref=%s', ms, unref)
    this._timeoutMs = ms
    this._timeoutUnref = !!unref
    this._resetTimeout(true)
  }

  destroy () {
    if (this.destroyed) return
    this._debug('destroy')
    this.end()
    return this
  }

  end (data) {
    if (this.destroyed || this.destroying) return
    this._debug('end')
    this._onUninterested()
    this._onChoke()
    return super.end(data)
  }

  /**
   * Use the specified protocol extension.
   * @param  {function} Extension
   */
  use (Extension) {
    const name = Extension.prototype.name
    if (!name) {
      throw new Error('Extension class requires a "name" property on the prototype')
    }
    this._debug('use extension.name=%s', name)

    const ext = this._nextExt
    const handler = new Extension(this)

    function noop () {}

    if (typeof handler.onHandshake !== 'function') {
      handler.onHandshake = noop
    }
    if (typeof handler.onExtendedHandshake !== 'function') {
      handler.onExtendedHandshake = noop
    }
    if (typeof handler.onMessage !== 'function') {
      handler.onMessage = noop
    }

    this.extendedMapping[ext] = name
    this._ext[name] = handler
    this[name] = handler

    this._nextExt += 1
  }

  //
  // OUTGOING MESSAGES
  //

  /**
   * Message "keep-alive": <len=0000>
   */
  keepAlive () {
    this._debug('keep-alive')
    this._push(MESSAGE_KEEP_ALIVE)
  }

  /**
   * Start the PE/MSE handshake as initiator.
   * @param {string} infoHash hex-encoded info hash
   */
  startEncryption (infoHash) {
    if (!this._peEnabled) return
    this._infoHash = infoHash
    this._encryptor = new MessageStreamEncryptor(infoHash)
    const step1 = this._encryptor.generateStepA1()
    this._push(step1)
    this._peState = 'sentPe1'
    this._debug('PE: sent step 1 (initiator)')
  }

  /**
   * Message: "handshake" <pstrlen><pstr><reserved><info_hash><peer_id>
   * @param  {Uint8Array|string} infoHash (as Buffer or *hex* string)
   * @param  {Uint8Array|string} peerId
   * @param  {Object} extensions
   */
  handshake (infoHash, peerId, extensions) {
    let infoHashBuffer
    let peerIdBuffer
    if (typeof infoHash === 'string') {
      infoHash = infoHash.toLowerCase()
      infoHashBuffer = hex2arr(infoHash)
    } else {
      infoHashBuffer = infoHash
      infoHash = arr2hex(infoHashBuffer)
    }
    if (typeof peerId === 'string') {
      peerIdBuffer = hex2arr(peerId)
    } else {
      peerIdBuffer = peerId
      peerId = arr2hex(peerIdBuffer)
    }

    this._infoHash = infoHashBuffer

    if (infoHashBuffer.length !== 20 || peerIdBuffer.length !== 20) {
      throw new Error('infoHash and peerId MUST have length 20')
    }

    this._debug('handshake i=%s p=%s exts=%o', infoHash, peerId, extensions)

    const reserved = new Uint8Array(MESSAGE_RESERVED)

    this.extensions = {
      extended: true,
      dht: !!(extensions && extensions.dht),
      fast: !!(extensions && extensions.fast)
    }

    reserved[5] |= 0x10 // enable extended message
    if (this.extensions.dht) reserved[7] |= 0x01
    if (this.extensions.fast) reserved[7] |= 0x04

    // BEP6 Fast Extension: The extension is enabled only if both ends of the connection set this bit.
    if (this.extensions.fast && this.peerExtensions.fast) {
      this._debug('fast extension is enabled')
      this.hasFast = true
    }
    this._push(concat([MESSAGE_PROTOCOL, reserved, infoHashBuffer, peerIdBuffer]))
    this._handshakeSent = true

    if (this.peerExtensions.extended && !this._extendedHandshakeSent) {
      // Peer's handshake indicated support already
      // (incoming connection)
      this._sendExtendedHandshake()
    }
  }

  /* Peer supports BEP-0010, send extended handshake.
   *
   * This comes after the 'handshake' event to give the user a chance to populate
   * `this.extendedHandshake` and `this.extendedMapping` before the extended handshake
   * is sent to the remote peer.
   */
  _sendExtendedHandshake () {
    // Create extended message object from registered extensions
    const msg = Object.assign({}, this.extendedHandshake)
    msg.m = {}
    for (const ext in this.extendedMapping) {
      const name = this.extendedMapping[ext]
      msg.m[name] = Number(ext)
    }

    // Send extended handshake
    this.extended(0, bencode.encode(msg))
    this._extendedHandshakeSent = true
  }

  /**
   * Message "choke": <len=0001><id=0>
   */
  choke () {
    if (this.amChoking) return
    this.amChoking = true
    this._debug('choke')
    this._push(MESSAGE_CHOKE)

    if (this.hasFast) {
      // BEP6: If a peer sends a choke, it MUST reject all requests from the peer to whom the choke
      // was sent except it SHOULD NOT reject requests for pieces that are in the allowed fast set.
      let allowedCount = 0
      while (this.peerRequests.length > allowedCount) { // until only allowed requests are left
        const request = this.peerRequests[allowedCount] // first non-allowed request
        if (this.allowedFastSet.includes(request.piece)) {
          ++allowedCount // count request as allowed
        } else {
          this.reject(request.piece, request.offset, request.length) // removes from this.peerRequests
        }
      }
    } else {
      while (this.peerRequests.length) {
        this.peerRequests.pop()
      }
    }
  }

  /**
   * Message "unchoke": <len=0001><id=1>
   */
  unchoke () {
    if (!this.amChoking) return
    this.amChoking = false
    this._debug('unchoke')
    this._push(MESSAGE_UNCHOKE)
  }

  /**
   * Message "interested": <len=0001><id=2>
   */
  interested () {
    if (this.amInterested) return
    this.amInterested = true
    this._debug('interested')
    this._push(MESSAGE_INTERESTED)
  }

  /**
   * Message "uninterested": <len=0001><id=3>
   */
  uninterested () {
    if (!this.amInterested) return
    this.amInterested = false
    this._debug('uninterested')
    this._push(MESSAGE_UNINTERESTED)
  }

  /**
   * Message "have": <len=0005><id=4><piece index>
   * @param  {number} index
   */
  have (index) {
    this._debug('have %d', index)
    this._message(4, [index], null)
  }

  /**
   * Message "bitfield": <len=0001+X><id=5><bitfield>
   * @param  {BitField|Buffer} bitfield
   */
  bitfield (bitfield) {
    this._debug('bitfield')
    if (!ArrayBuffer.isView(bitfield)) bitfield = bitfield.buffer
    this._message(5, [], bitfield)
  }

  /**
   * Message "request": <len=0013><id=6><index><begin><length>
   * @param  {number}   index
   * @param  {number}   offset
   * @param  {number}   length
   * @param  {function} cb
   */
  request (index, offset, length, cb) {
    if (!cb) cb = () => {}
    if (this._finished) return cb(new Error('wire is closed'))

    if (this.peerChoking && !(this.hasFast && this.peerAllowedFastSet.includes(index))) {
      return cb(new Error('peer is choking'))
    }

    this._debug('request index=%d offset=%d length=%d', index, offset, length)

    this.requests.push(new Request(index, offset, length, cb))
    if (!this._timeout) {
      this._resetTimeout(true)
    }
    this._message(6, [index, offset, length], null)
  }

  /**
   * Message "piece": <len=0009+X><id=7><index><begin><block>
   * @param  {number} index
   * @param  {number} offset
   * @param  {Uint8Array} buffer
   */
  piece (index, offset, buffer) {
    this._debug('piece index=%d offset=%d', index, offset)
    this._message(7, [index, offset], buffer)
    this.uploaded += buffer.length
    this.uploadSpeed(buffer.length)
    this.emit('upload', buffer.length)
  }

  /**
   * Message "cancel": <len=0013><id=8><index><begin><length>
   * @param  {number} index
   * @param  {number} offset
   * @param  {number} length
   */
  cancel (index, offset, length) {
    this._debug('cancel index=%d offset=%d length=%d', index, offset, length)
    this._callback(
      this._pull(this.requests, index, offset, length),
      new Error('request was cancelled'),
      null
    )
    this._message(8, [index, offset, length], null)
  }

  /**
   * Message: "port" <len=0003><id=9><listen-port>
   * @param {Number} port
   */
  port (port) {
    this._debug('port %d', port)
    const message = new Uint8Array(MESSAGE_PORT)
    const view = new DataView(message.buffer)
    view.setUint16(5, port)
    this._push(message)
  }

  /**
   * Message: "suggest" <len=0x0005><id=0x0D><piece index> (BEP6)
   * @param {number} index
   */
  suggest (index) {
    if (!this.hasFast) throw Error('fast extension is disabled')
    this._debug('suggest %d', index)
    this._message(0x0D, [index], null)
  }

  /**
   * Message: "have-all" <len=0x0001><id=0x0E> (BEP6)
   */
  haveAll () {
    if (!this.hasFast) throw Error('fast extension is disabled')
    this._debug('have-all')
    this._push(MESSAGE_HAVE_ALL)
  }

  /**
   * Message: "have-none" <len=0x0001><id=0x0F> (BEP6)
   */
  haveNone () {
    if (!this.hasFast) throw Error('fast extension is disabled')
    this._debug('have-none')
    this._push(MESSAGE_HAVE_NONE)
  }

  /**
   * Message "reject": <len=0x000D><id=0x10><index><offset><length> (BEP6)
   * @param  {number}   index
   * @param  {number}   offset
   * @param  {number}   length
   */
  reject (index, offset, length) {
    if (!this.hasFast) throw Error('fast extension is disabled')
    this._debug('reject index=%d offset=%d length=%d', index, offset, length)
    this._pull(this.peerRequests, index, offset, length)
    this._message(0x10, [index, offset, length], null)
  }

  /**
   * Message: "allowed-fast" <len=0x0005><id=0x11><piece index> (BEP6)
   * @param {number} index
   */
  allowedFast (index) {
    if (!this.hasFast) throw Error('fast extension is disabled')
    this._debug('allowed-fast %d', index)
    if (!this.allowedFastSet.includes(index)) this.allowedFastSet.push(index)
    this._message(0x11, [index], null)
  }

  /**
   * Message: "extended" <len=0005+X><id=20><ext-number><payload>
   * @param  {number|string} ext
   * @param  {Object} obj
   */
  extended (ext, obj) {
    this._debug('extended ext=%s', ext)
    if (typeof ext === 'string' && this.peerExtendedMapping[ext]) {
      ext = this.peerExtendedMapping[ext]
    }
    if (typeof ext === 'number') {
      const extId = new Uint8Array([ext])
      const buf = ArrayBuffer.isView(obj) ? obj : bencode.encode(obj)

      this._message(20, [], concat([extId, buf]))
    } else {
      throw new Error(`Unrecognized extension: ${ext}`)
    }
  }

  /**
   * Sets the encryption method for this wire, as per PSE/ME specification
   * Called by conn-pool when it resolves the infoHash from a crypto-infohash event.
   * Initializes the responder's ciphers and resumes pe3 processing.
   * @param {string} infoHash hex-encoded info hash
   */
  async setInfoHash (infoHash) {
    this._infoHash = infoHash
    this._encryptor.skeyHex = infoHash.toLowerCase()
    await this._encryptor._initializeCiphers('B')
    this._parsePe3Encrypted()
    if (this._pePendingResolver) {
      this._pePendingResolver()
      this._pePendingResolver = null
    }
  }

  /**
   * Send a message to the remote peer.
   */
  _message (id, numbers, data) {
    const dataLength = data ? data.length : 0
    const buffer = new Uint8Array(5 + (4 * numbers.length))

    setUint32(buffer, 0, buffer.length + dataLength - 4)
    buffer[4] = id
    for (let i = 0; i < numbers.length; i++) {
      setUint32(buffer, 5 + (4 * i), numbers[i])
    }

    this._push(buffer)
    if (data) this._push(data)
  }

  _push (data) {
    if (this._finished) return
    if (this._encryptionMethod === 2 && this._cryptoHandshakeDone && this._encryptor) {
      data = this._encryptor.encrypt(data)
    }
    return this.push(data)
  }

  //
  // INCOMING MESSAGES
  //

  _onKeepAlive () {
    this._debug('got keep-alive')
    this.emit('keep-alive')
  }

  /**
   * Advance the PE state machine when conditions are met
   * (e.g. infoHash is available, previous step completed).
   */
  async _advanceEncryption () {
    if (this._peState === 'gotPe2' && this._infoHash) {
      // Initiator: send step 3
      const step3 = await this._encryptor.generateStepA3()
      // Parse step4 before pushing step3 (may arrive synchronously)
      this._peState = 'sentPe3'
      this._debug('PE: sent step 3 (initiator)')
      this._parsePe4()
      this._push(step3)
    }
    if (this._peState === 'gotPe3' && this._infoHash) {
      // Responder: send step 4
      const step4 = this._encryptor.generateStepB4()
      // Already encrypted - must not be re-encrypted
      this._push(step4)
      this._cryptoHandshakeDone = true
      this._encryptionMethod = 2
      this._encryptor._isEncrypted = true
      // Decrypt data that was buffered before crypto was established
      if (this._bufferSize > 0) {
        const buf = concat(this._buffer, this._bufferSize)
        this._buffer = [this._encryptor.decrypt(buf)]
      }
      this._peState = 'done'
      this._debug('PE: sent step 4 (responder), crypto handshake done')
      this.emit('crypto-handshake')
      // If handshake was already received via IA, don't re-parse it
      if (!this.peerId) this._parseHandshake(null)
    }
  }

  _onHandshake (infoHashBuffer, peerIdBuffer, extensions) {
    const infoHash = arr2hex(infoHashBuffer)
    const peerId = arr2hex(peerIdBuffer)

    this._debug('got handshake i=%s p=%s exts=%o', infoHash, peerId, extensions)

    this.peerId = peerId
    this.peerIdBuffer = peerIdBuffer
    this.peerExtensions = extensions

    // BEP6 Fast Extension: The extension is enabled only if both ends of the connection set this bit.
    if (this.extensions.fast && this.peerExtensions.fast) {
      this._debug('fast extension is enabled')
      this.hasFast = true
    }

    this.emit('handshake', infoHash, peerId, extensions)

    for (const name in this._ext) {
      this._ext[name].onHandshake(infoHash, peerId, extensions)
    }

    if (extensions.extended && this._handshakeSent &&
        !this._extendedHandshakeSent) {
      // outgoing connection
      this._sendExtendedHandshake()
    }
  }

  _onChoke () {
    this.peerChoking = true
    this._debug('got choke')
    this.emit('choke')
    if (!this.hasFast) {
      // BEP6 Fast Extension: Choke no longer implicitly rejects all pending requests
      while (this.requests.length) {
        this._callback(this.requests.pop(), new Error('peer is choking'), null)
      }
    }
  }

  _onUnchoke () {
    this.peerChoking = false
    this._debug('got unchoke')
    this.emit('unchoke')
  }

  _onInterested () {
    this.peerInterested = true
    this._debug('got interested')
    this.emit('interested')
  }

  _onUninterested () {
    this.peerInterested = false
    this._debug('got uninterested')
    this.emit('uninterested')
  }

  _onHave (index) {
    if (this.peerPieces.get(index)) return
    this._debug('got have %d', index)

    this.peerPieces.set(index, true)
    this.emit('have', index)
  }

  _onBitField (buffer) {
    this.peerPieces = new BitField(buffer)
    this._debug('got bitfield')
    this.emit('bitfield', this.peerPieces)
  }

  _onRequest (index, offset, length) {
    if (this.amChoking && !(this.hasFast && this.allowedFastSet.includes(index))) {
      // BEP6: If a peer receives a request from a peer its choking, the peer receiving
      // the request SHOULD send a reject unless the piece is in the allowed fast set.
      if (this.hasFast) this.reject(index, offset, length)
      return
    }
    this._debug('got request index=%d offset=%d length=%d', index, offset, length)

    const respond = (err, buffer) => {
      if (request !== this._pull(this.peerRequests, index, offset, length)) return
      if (err) {
        this._debug('error satisfying request index=%d offset=%d length=%d (%s)', index, offset, length, err.message)
        if (this.hasFast) this.reject(index, offset, length)
        return
      }
      this.piece(index, offset, buffer)
    }

    const request = new Request(index, offset, length, respond)
    this.peerRequests.push(request)
    this.emit('request', index, offset, length, respond)
  }

  _onPiece (index, offset, buffer) {
    this._debug('got piece index=%d offset=%d', index, offset)
    this._callback(this._pull(this.requests, index, offset, buffer.length), null, buffer)
    this.downloaded += buffer.length
    this.downloadSpeed(buffer.length)
    this.emit('download', buffer.length)
    this.emit('piece', index, offset, buffer)
  }

  _onCancel (index, offset, length) {
    this._debug('got cancel index=%d offset=%d length=%d', index, offset, length)
    this._pull(this.peerRequests, index, offset, length)
    this.emit('cancel', index, offset, length)
  }

  _onPort (port) {
    this._debug('got port %d', port)
    this.emit('port', port)
  }

  _onSuggest (index) {
    if (!this.hasFast) {
      // BEP6: the peer MUST close the connection
      this._debug('Error: got suggest whereas fast extension is disabled')
      this.destroy()
      return
    }
    this._debug('got suggest %d', index)
    this.emit('suggest', index)
  }

  _onHaveAll () {
    if (!this.hasFast) {
      // BEP6: the peer MUST close the connection
      this._debug('Error: got have-all whereas fast extension is disabled')
      this.destroy()
      return
    }
    this._debug('got have-all')
    this.peerPieces = new HaveAllBitField()
    this.emit('have-all')
  }

  _onHaveNone () {
    if (!this.hasFast) {
      // BEP6: the peer MUST close the connection
      this._debug('Error: got have-none whereas fast extension is disabled')
      this.destroy()
      return
    }
    this._debug('got have-none')
    this.emit('have-none')
  }

  _onReject (index, offset, length) {
    if (!this.hasFast) {
      // BEP6: the peer MUST close the connection
      this._debug('Error: got reject whereas fast extension is disabled')
      this.destroy()
      return
    }
    this._debug('got reject index=%d offset=%d length=%d', index, offset, length)
    this._callback(
      this._pull(this.requests, index, offset, length),
      new Error('request was rejected'),
      null
    )
    this.emit('reject', index, offset, length)
  }

  _onAllowedFast (index) {
    if (!this.hasFast) {
      // BEP6: the peer MUST close the connection
      this._debug('Error: got allowed-fast whereas fast extension is disabled')
      this.destroy()
      return
    }
    this._debug('got allowed-fast %d', index)
    if (!this.peerAllowedFastSet.includes(index)) this.peerAllowedFastSet.push(index)
    if (this.peerAllowedFastSet.length > ALLOWED_FAST_SET_MAX_LENGTH) this.peerAllowedFastSet.shift()
    this.emit('allowed-fast', index)
  }

  _onExtended (ext, buf) {
    if (ext === 0) {
      let info
      try {
        info = bencode.decode(buf)
      } catch (err) {
        this._debug('ignoring invalid extended handshake: %s', err.message || err)
      }

      if (!info) return
      this.peerExtendedHandshake = info

      if (typeof info.m === 'object') {
        for (const name in info.m) {
          this.peerExtendedMapping[name] = Number(info.m[name].toString())
        }
      }
      for (const name in this._ext) {
        if (this.peerExtendedMapping[name]) {
          this._ext[name].onExtendedHandshake(this.peerExtendedHandshake)
        }
      }
      this._debug('got extended handshake')
      this.emit('extended', 'handshake', this.peerExtendedHandshake)
    } else {
      if (this.extendedMapping[ext]) {
        ext = this.extendedMapping[ext] // friendly name for extension
        if (this._ext[ext]) {
          // there is an registered extension handler, so call it
          this._ext[ext].onMessage(buf)
        }
      }
      this._debug('got extended message ext=%s', ext)
      this.emit('extended', ext, buf)
    }
  }

  _onTimeout () {
    this._debug('request timed out')
    this._callback(this.requests.shift(), new Error('request has timed out'), null)
    this.emit('timeout')
  }

  /**
   * Duplex stream method. Called whenever the remote peer has data for us. Data that the
   * remote peer sends gets buffered (i.e. not actually processed) until the right number
   * of bytes have arrived, determined by the last call to `this._parse(number, callback)`.
   * Once enough bytes have arrived to process the message, the callback function
   * (i.e. `this._parser`) gets called with the full buffer of data.
   * @param  {Uint8Array} data
   * @param  {function} cb
   */
  _write (data, cb) {
    if (this._encryptionMethod === 2 && this._cryptoHandshakeDone && this._encryptor) {
      data = this._encryptor.decrypt(data)
    }
    this._bufferSize += data.length
    this._buffer.push(data)
    if (this._buffer.length > 1) {
      this._buffer = [concat(this._buffer, this._bufferSize)]
    }
    this._processBuffer()
    cb(null)
  }

  /**
   * Process buffered data through the parser state machine.
   * Safe for async parser callbacks (detects Promises and prevents re-entrance).
   */
  async _processBuffer () {
    if (this._cryptoSyncPattern) {
      const index = this._encryptor._indexOf(this._buffer[0], this._cryptoSyncPattern)
      if (index !== -1) {
        this._buffer[0] = this._buffer[0].slice(index + this._cryptoSyncPattern.length)
        this._bufferSize -= (index + this._cryptoSyncPattern.length)
        this._cryptoSyncPattern = null
      } else if (this._bufferSize > this._waitMaxBytes + this._cryptoSyncPattern.length) {
        this._debug('Error: could not resynchronize')
        this.destroy()
        return
      }
      if (this._cryptoSyncPattern) return
    }

    if (this._asyncParsePending) return

    while (this._bufferSize >= this._parserSize) {
      // Stop if a sync pattern was set in the callback (e.g. from _parsePe3)
      if (this._cryptoSyncPattern) break
      if (this._parserSize === 0) {
        this._parser(new Uint8Array())
      } else {
        const buf = this._buffer[0]
        this._bufferSize -= this._parserSize
        this._buffer = this._bufferSize
          ? [buf.subarray(this._parserSize)]
          : []
        const result = this._parser(buf.subarray(0, this._parserSize))
        if (result instanceof Promise) {
          this._asyncParsePending = true
          try {
            await result
          } catch (err) {
            this._debug('Error: async parse error %s', err.message || err)
          }
          this._asyncParsePending = false
          this._processBuffer()
          break
        }
      }
    }
  }

  _callback (request, err, buffer) {
    if (!request) return

    this._resetTimeout(!this.peerChoking && !this._finished)

    request.callback(err, buffer)
  }

  _resetTimeout (setAgain) {
    if (!setAgain || !this._timeoutMs || !this.requests.length) {
      clearTimeout(this._timeout)
      this._timeout = null
      this._timeoutExpiresAt = null
      return
    }

    const timeoutExpiresAt = Date.now() + this._timeoutMs

    if (this._timeout) {
      // If existing expiration is already within 5% of correct, it's close enough
      if (timeoutExpiresAt - this._timeoutExpiresAt < this._timeoutMs * 0.05) {
        return
      }
      clearTimeout(this._timeout)
    }

    this._timeoutExpiresAt = timeoutExpiresAt
    this._timeout = setTimeout(() => this._onTimeout(), this._timeoutMs)
    if (this._timeoutUnref && this._timeout.unref) this._timeout.unref()
  }

  /**
   * Takes a number of bytes that the local peer is waiting to receive from the remote peer
   * in order to parse a complete message, and a callback function to be called once enough
   * bytes have arrived.
   * @param  {number} size
   * @param  {function} parser
   */
  _parse (size, parser) {
    this._parserSize = size
    this._parser = parser
  }

  _parseUntil (pattern, maxBytes) {
    this._cryptoSyncPattern = pattern
    this._waitMaxBytes = maxBytes
  }

  /**
   * Handle the first 4 bytes of a message, to determine the length of bytes that must be
   * waited for in order to have the whole message.
   * @param  {Uint8Array} buffer
   */
  _onMessageLength (buffer) {
    const length = getUint32(buffer)
    if (length > 0) {
      this._parse(length, this._onMessage)
    } else {
      this._onKeepAlive()
      this._parse(4, this._onMessageLength)
    }
  }

  /**
   * Handle a message from the remote peer.
   * @param  {Uint8Array} buffer
   */
  _onMessage (buffer) {
    this._parse(4, this._onMessageLength)
    switch (buffer[0]) {
      case 0:
        return this._onChoke()
      case 1:
        return this._onUnchoke()
      case 2:
        return this._onInterested()
      case 3:
        return this._onUninterested()
      case 4:
        return this._onHave(getUint32(buffer, 1))
      case 5:
        return this._onBitField(buffer.subarray(1))
      case 6:
        return this._onRequest(
          getUint32(buffer, 1),
          getUint32(buffer, 5),
          getUint32(buffer, 9)
        )
      case 7:
        return this._onPiece(
          getUint32(buffer, 1),
          getUint32(buffer, 5),
          buffer.subarray(9)
        )
      case 8:
        return this._onCancel(
          getUint32(buffer, 1),
          getUint32(buffer, 5),
          getUint32(buffer, 9)
        )
      case 9:
        return this._onPort((buffer[1] << 8) | buffer[2])
      case 0x0D:
        return this._onSuggest(getUint32(buffer, 1))
      case 0x0E:
        return this._onHaveAll()
      case 0x0F:
        return this._onHaveNone()
      case 0x10:
        return this._onReject(
          getUint32(buffer, 1),
          getUint32(buffer, 5),
          getUint32(buffer, 9)
        )
      case 0x11:
        return this._onAllowedFast(getUint32(buffer, 1))
      case 20:
        return this._onExtended(buffer[1], buffer.subarray(2))
      default:
        this._debug('got unknown message')
        return this.emit('unknownmessage', buffer)
    }
  }

  _determineHandshakeType () {
    this._parse(1, pstrLenBuffer => {
      const pstrlen = pstrLenBuffer[0]
      if (pstrlen === 19) {
        this._parse(pstrlen + 48, this._onHandshakeBuffer)
      } else {
        this._parsePe1(pstrLenBuffer)
      }
    })
  }

  _parsePe1 (pubKeyPrefix) {
    this._parse(95, async pubKeySuffix => {
      this._encryptor = new MessageStreamEncryptor(null)
      this._encryptor.handleStepB1(concat([pubKeyPrefix, pubKeySuffix]))
      const step2 = this._encryptor.generateStepB2()
      this._push(step2)
      this._peState = 'sentPe2'
      this._debug('PE: handled step 1, sent step 2 (responder)')
      await this._parsePe3()
    })
  }

  _parsePe2 () {
    this._parse(96, async pubKey => {
      // Initiator: step 2 received from responder
      await this._encryptor.handleStepA2(pubKey)
      this._peState = 'gotPe2'
      this._debug('PE: handled step 2 (initiator)')
      await this._advanceEncryption()
    })
  }

  // Handles the unencrypted portion of step 4
  async _parsePe3 () {
    const hash1Buffer = await hash(concat([REQ1_STR, this._encryptor.S]))
    this._parseUntil(hash1Buffer, SYNC_MAX_BYTES)
    this._parse(20, async buffer => {
      const req3Hash = await hash(concat([REQ3_STR, this._encryptor.S]))
      const infoHashHash = arr2hex(xor(new Uint8Array(req3Hash), buffer))
      this._peState = 'gotPe3'
      this._debug('PE: handled step 3 XOR hash (responder)')
      this.emit('crypto-infohash', infoHashHash)
      await new Promise(resolve => {
        // Wait until generators have been set
        this._pePendingResolver = resolve
      })
    })
  }

  _parsePe3Encrypted () {
    this._parse(14, buffer => {
      // Decrypt VC (8) + crypto_provide (4) + padC_len (2)
      const decHeader = this._encryptor._decryptHandshake(buffer)
      const vc = decHeader.slice(0, 8)
      if (!equal(vc, VC)) {
        this._debug('Error: VC verification failed in pe3')
        this.destroy()
        return
      }
      const cryptoProvide = new DataView(decHeader.buffer, decHeader.byteOffset + 8, 4).getUint32(0, false)
      if ((cryptoProvide & 0x02) !== 0) {
        this._encryptionMethod = 2
      } else {
        this._debug('Error: RC4 not provided by peer')
        this.destroy()
        return
      }
      const padCLen = new DataView(decHeader.buffer, decHeader.byteOffset + 12, 2).getUint16(0, false)
      this._parse(padCLen, padCBuf => {
        this._encryptor._decryptHandshake(padCBuf) // discard padC
        this._parse(2, iaLenBuf => {
          const iaLen = new DataView(this._encryptor._decryptHandshake(iaLenBuf).buffer).getUint16(0, false)
          this._parse(iaLen, iaBuffer => {
            const ia = this._encryptor._decryptHandshake(iaBuffer)
            // Check if IA contains a BT handshake
            if (ia.length > 0 && ia[0] === 19 && arr2text(ia.slice(1, 20)) === 'BitTorrent protocol') {
              this._onHandshakeBuffer(ia.slice(1))
            }
            // Complete crypto handshake - send pe4
            this._advanceEncryption()
          })
        })
      })
    })
  }

  _parsePe4 () {
    // synchronize on ENCRYPT(VC).
    // since we encrypt using bitwise xor, decryption and encryption are the same operation.
    // calling _decryptHandshake here advances the decrypt generator keystream forward 8 bytes
    const vcBufferEncrypted = this._encryptor._decryptHandshake(VC)
    this._parseUntil(vcBufferEncrypted, SYNC_MAX_BYTES)
    this._parse(6, buffer => {
      const peerSelect = this._encryptor._decryptHandshake(buffer)
      const selectMethod = new DataView(peerSelect.buffer, peerSelect.byteOffset, 4).getUint32(0, false)
      if (selectMethod !== 2) {
        this._debug('Error: peer selected non-RC4 method (%s)', selectMethod.toString(16))
        this.destroy()
        return
      }
      this._encryptionMethod = 2
      const padDLen = new DataView(peerSelect.buffer, peerSelect.byteOffset + 4, 2).getUint16(0, false)
      this._parse(padDLen, padDBuf => {
        this._encryptor._decryptHandshake(padDBuf)
        this._cryptoHandshakeDone = true
        this._encryptionMethod = 2
        this._encryptor._isEncrypted = true
        // Decrypt data that was buffered before crypto was established
        if (this._bufferSize > 0) {
          const buf = concat(this._buffer, this._bufferSize)
          this._buffer = [this._encryptor.decrypt(buf)]
        }
        this._peState = 'done'
        this._debug('PE: handled step 4, crypto handshake done')
        this.emit('crypto-handshake')
        this._parseHandshake(null)
      })
    })
  }

  /**
   * Reads the handshake as specified by the bittorrent wire protocol.
   */
  _parseHandshake () {
    this._parse(1, buffer => {
      const pstrlen = buffer[0]
      if (pstrlen !== 19) {
        this._debug('Error: wire not speaking BitTorrent protocol (%s)', pstrlen.toString())
        this.end()
        return
      }
      this._parse(pstrlen + 48, this._onHandshakeBuffer)
    })
  }

  _onHandshakeBuffer (handshake) {
    const protocol = handshake.slice(0, 19)
    if (arr2text(protocol) !== 'BitTorrent protocol') {
      this._debug('Error: wire not speaking BitTorrent protocol (%s)', arr2text(protocol))
      this.end()
      return
    }
    handshake = handshake.slice(19)
    this._onHandshake(handshake.slice(8, 28), handshake.slice(28, 48), {
      dht: !!(handshake[7] & 0x01), // see bep_0005
      fast: !!(handshake[7] & 0x04), // see bep_0006
      extended: !!(handshake[5] & 0x10) // see bep_0010
    })
    this._parse(4, this._onMessageLength)
  }

  _onFinish () {
    this._finished = true

    this.push(null) // stream cannot be half open, so signal the end of it
    while (this.read()) {
      // body intentionally empty
      // consume and discard the rest of the stream data
    }

    clearInterval(this._keepAliveInterval)
    this._parse(Number.MAX_VALUE, () => {})
    while (this.peerRequests.length) {
      this.peerRequests.pop()
    }
    while (this.requests.length) {
      this._callback(this.requests.pop(), new Error('wire was closed'), null)
    }
  }

  _debug (...args) {
    args[0] = `[${this._debugId}] ${args[0]}`
    debug(...args)
  }

  _pull (requests, piece, offset, length) {
    for (let i = 0; i < requests.length; i++) {
      const req = requests[i]
      if (req.piece === piece && req.offset === offset && req.length === length) {
        arrayRemove(requests, i)
        return req
      }
    }
    return null
  }
}

export default Wire
