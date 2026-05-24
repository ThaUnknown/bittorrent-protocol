import crypto from 'crypto'
import RC4 from 'rc4'
import { concat, equal, hex2arr, arr2hex, text2arr, randomBytes, hash } from 'uint8-util'
import Debug from 'debug'

const debug = Debug('bittorrent-protocol')

const DH_PRIME = 'ffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a63a36210000000000090563'
const DH_GENERATOR = 2

export const REQ1_STR = text2arr('req1')
export const REQ2_STR = text2arr('req2')
export const REQ3_STR = text2arr('req3')
export const KEYA_STR = text2arr('keyA')
export const KEYB_STR = text2arr('keyB')

export const VC = new Uint8Array([0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])

export function xor (a, b) {
  for (let len = a.length; len--;) a[len] ^= b[len]
  return a
}

/**
 * Message Stream Encryption / Protocol Encryption (MSE/PE) crypto engine.
 */
export class MessageStreamEncryptor {
  /**
   * @param {string} skeyHex hex-encoded info hash (SKEY)
   */
  constructor (skeyHex) {
    this.skeyHex = skeyHex
    this.dh = crypto.createDiffieHellman(DH_PRIME, 'hex', DH_GENERATOR)
    this._isEncrypted = false
    this.S = null
    this.encryptCipher = null
    this.decryptCipher = null
    this.selectedCrypto = 0x02 // RC4
    this.ya = null
    this.cryptoProvide = 0
  }

  /** DH Ya + PadA */
  generateStepA1 () {
    const ya = hex2arr(this.dh.generateKeys('hex'))
    const padA = randomBytes(Math.floor(Math.random() * 513))
    return concat([ya, padA])
  }

  /** Compute S from Yb, init ciphers */
  async handleStepA2 (step2Data) {
    const yb = step2Data.slice(0, 96)
    this.S = hex2arr(this.dh.computeSecret(yb, null, 'hex'))
    await this._initializeCiphers('A')
  }

  /** Hashes, crypto_provide, padC, IA (all encrypted) */
  async generateStepA3 (initialA = new Uint8Array(0)) {
    const req1Hash = await hash(concat([REQ1_STR, this.S]))
    const req2Hash = await hash(concat([REQ2_STR, hex2arr(this.skeyHex)]))
    const req3Hash = await hash(concat([REQ3_STR, this.S]))
    const xorHash = xor(req2Hash, req3Hash)

    const cryptoProvideArray = new Uint8Array(4)
    new DataView(cryptoProvideArray.buffer).setUint32(0, 0x01 | 0x02, false) // PLAINTEXT | RC4

    const padC = randomBytes(Math.floor(Math.random() * 513))
    const lenPadC = new Uint8Array(2)
    new DataView(lenPadC.buffer).setUint16(0, padC.length, false)
    const lenIA = new Uint8Array(2)
    new DataView(lenIA.buffer).setUint16(0, initialA.length, false)

    const plaintext = concat([VC, cryptoProvideArray, lenPadC, padC, lenIA])
    const encryptedPart1 = this._encryptHandshake(plaintext)
    const encryptedPart2 = this._encryptHandshake(initialA)

    return concat([req1Hash, xorHash, encryptedPart1, encryptedPart2])
  }

  /** Verify VC, extract crypto_select */
  handleStepA4 (step4Data) {
    const decrypted = this._decryptHandshake(step4Data)
    const vc = decrypted.slice(0, 8)
    if (!equal(vc, VC)) {
      debug('Initiator: VC verification failed')
      return false
    }
    this.selectedCrypto = new DataView(decrypted.buffer, decrypted.byteOffset + 8, 4).getUint32(0, false)
    const padDLen = new DataView(decrypted.buffer, decrypted.byteOffset + 12, 2).getUint16(0, false)
    this._isEncrypted = true
    return padDLen
  }

  //
  // RESPONDER STEPS
  //

  /** Extract Ya from initiator */
  handleStepB1 (step1Data) {
    this.ya = step1Data.slice(0, 96)
  }

  /** DH Yb + PadB */
  generateStepB2 () {
    const yb = hex2arr(this.dh.generateKeys('hex'))
    this.S = hex2arr(this.dh.computeSecret(this.ya, null, 'hex'))
    const padB = randomBytes(Math.floor(Math.random() * 513))
    return concat([yb, padB])
  }

  /** Verify hashes, decrypt IA */
  async handleStepB3 (step3Data) {
    const req1Hash = await hash(concat([REQ1_STR, this.S]))
    const syncPoint = this._indexOf(step3Data, req1Hash)

    if (syncPoint === -1) {
      debug('Responder: Could not synchronize on HASH(req1, S)')
      return null
    }

    const xorHashOffset = syncPoint + 20
    const receivedXorHash = step3Data.slice(xorHashOffset, xorHashOffset + 20)
    const req2Hash = await hash(concat([REQ2_STR, hex2arr(this.skeyHex)]))
    const req3Hash = await hash(concat([REQ3_STR, this.S]))
    const expectedXorHash = xor(req2Hash, req3Hash)

    if (!equal(receivedXorHash, expectedXorHash)) {
      debug('Responder: SKEY hash verification failed')
      return null
    }

    const encryptedData = step3Data.slice(xorHashOffset + 20)
    const decrypted = this._decryptHandshake(encryptedData)
    const vc = decrypted.slice(0, 8)
    if (!equal(vc, VC)) {
      debug('Responder: VC verification failed')
      return null
    }

    this.cryptoProvide = new DataView(decrypted.buffer, decrypted.byteOffset + 8, 4).getUint32(0, false)
    const padCLen = new DataView(decrypted.buffer, decrypted.byteOffset + 12, 2).getUint16(0, false)

    // Extract info hash hash: HASH('req2', SKEY) which we computed as req2Hash
    const infoHashHash = arr2hex(req2Hash)

    const iaLenOffset = 14 + padCLen
    const iaLen = new DataView(decrypted.buffer, decrypted.byteOffset + iaLenOffset, 2).getUint16(0, false)
    const ia = decrypted.slice(iaLenOffset + 2, iaLenOffset + 2 + iaLen)

    if ((this.cryptoProvide & 0x02) !== 0) {
      this.selectedCrypto = 0x02
    } else if ((this.cryptoProvide & 0x01) !== 0) {
      this.selectedCrypto = 0x01
    } else {
      debug('Responder: No acceptable crypto method provided')
      return null
    }

    this._isEncrypted = true
    return { infoHashHash, ia }
  }

  /** Encrypted VC + crypto_select + padD */
  generateStepB4 () {
    const cryptoSelectArray = new Uint8Array(4)
    new DataView(cryptoSelectArray.buffer).setUint32(0, this.selectedCrypto, false)
    const padD = randomBytes(Math.floor(Math.random() * 513))
    const lenPadD = new Uint8Array(2)
    new DataView(lenPadD.buffer).setUint16(0, padD.length, false)

    const plaintext = concat([VC, cryptoSelectArray, lenPadD, padD])
    return this._encryptHandshake(plaintext)
  }

  //
  // PAYLOAD CRYPTO
  //

  encrypt (data) {
    if (!this._isEncrypted || this.selectedCrypto !== 0x02) return data
    return this._encryptHandshake(data)
  }

  decrypt (data) {
    if (!this._isEncrypted || this.selectedCrypto !== 0x02) return data
    return this._decryptHandshake(data)
  }

  async _initializeCiphers (party) {
    const keyA = await hash(concat([KEYA_STR, this.S, hex2arr(this.skeyHex)]))
    const keyB = await hash(concat([KEYB_STR, this.S, hex2arr(this.skeyHex)]))

    const encryptKey = party === 'A' ? keyA : keyB
    const decryptKey = party === 'A' ? keyB : keyA

    this.encryptCipher = new RC4([...encryptKey])
    this.decryptCipher = new RC4([...decryptKey])

    for (let i = 0; i < 1024; i++) {
      this.encryptCipher.randomByte()
      this.decryptCipher.randomByte()
    }
  }

  _encryptHandshake (buf) {
    const crypt = new Uint8Array(buf)
    for (let i = 0; i < buf.length; i++) {
      crypt[i] ^= this.encryptCipher.randomByte()
    }
    return crypt
  }

  _decryptHandshake (buf) {
    const decrypt = new Uint8Array(buf)
    for (let i = 0; i < buf.length; i++) {
      decrypt[i] ^= this.decryptCipher.randomByte()
    }
    return decrypt
  }

  _indexOf (source, find) {
    for (let i = 0; i <= source.length - find.length; i++) {
      let found = true
      for (let j = 0; j < find.length; j++) {
        if (source[i + j] !== find[j]) { found = false; break }
      }
      if (found) return i
    }
    return -1
  }
}
