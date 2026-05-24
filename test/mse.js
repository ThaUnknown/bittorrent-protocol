import crypto from 'crypto'
import test from 'tape'
import Wire from 'bittorrent-protocol'
import { concat, arr2hex, arr2text, hex2arr, randomBytes, equal, text2arr } from 'uint8-util'
import { MessageStreamEncryptor } from '../mse.js'

function linkWires (a, b) {
  a._push = function (data) {
    const encrypted = (this._encryptionMethod === 2 && this._cryptoHandshakeDone && this._encryptor) ? this._encryptor.encrypt(data) : data
    this.push(encrypted)
    b.write(encrypted)
  }
  b._push = function (data) {
    const encrypted = (this._encryptionMethod === 2 && this._cryptoHandshakeDone && this._encryptor) ? this._encryptor.encrypt(data) : data
    this.push(encrypted)
    a.write(encrypted)
  }
}

test('PE: wire-to-wire full handshake', t => {
  t.plan(2)

  const infoHash = arr2hex(randomBytes(20))
  const wireA = new Wire('tcpOutgoing', 0, true)
  const wireB = new Wire('tcpIncoming', 0, true)

  linkWires(wireA, wireB)

  wireB.once('crypto-infohash', () => wireB.setInfoHash(infoHash).then(() => {}))

  wireA.once('crypto-handshake', () => t.pass('initiator crypto handshake done'))
  wireB.once('crypto-handshake', () => t.pass('responder crypto handshake done'))

  wireA.startEncryption(infoHash)
})

test('PE: handshake state transitions', t => {
  t.plan(8)

  const infoHash = arr2hex(randomBytes(20))
  const wireA = new Wire('tcpOutgoing', 0, true)
  const wireB = new Wire('tcpIncoming', 0, true)

  linkWires(wireA, wireB)

  t.equal(wireA._peState, 'idle', 'initiator starts idle')
  t.equal(wireB._peState, 'idle', 'responder starts idle')

  wireB.once('crypto-infohash', () => wireB.setInfoHash(infoHash).then(() => {}))

  wireA.once('crypto-handshake', () => {
    t.equal(wireA._peState, 'done', 'initiator peState done')
    t.equal(wireA._encryptionMethod, 2, 'initiator using RC4')
    t.ok(wireA._cryptoHandshakeDone, 'initiator crypto handshake flagged')
  })

  wireB.once('crypto-handshake', () => {
    t.equal(wireB._peState, 'done', 'responder peState done')
    t.equal(wireB._encryptionMethod, 2, 'responder using RC4')
    t.ok(wireB._cryptoHandshakeDone, 'responder crypto handshake flagged')
  })

  wireA.startEncryption(infoHash)
})

test('PE: wire-to-wire with BT handshake exchange', t => {
  t.plan(4)

  const infoHash = arr2hex(randomBytes(20))
  const peerIdA = arr2hex(randomBytes(20))
  const peerIdB = arr2hex(randomBytes(20))

  const wireA = new Wire('tcpOutgoing', 0, true)
  const wireB = new Wire('tcpIncoming', 0, true)

  linkWires(wireA, wireB)

  wireB.once('crypto-infohash', () => wireB.setInfoHash(infoHash).then(() => {}))

  wireA.once('crypto-handshake', () => {
    wireA.handshake(infoHash, peerIdA, { dht: false, fast: true })
  })

  wireB.once('crypto-handshake', () => {
    wireB.handshake(infoHash, peerIdB, { dht: false, fast: true })
  })

  wireA.once('handshake', (gotIH, gotPI) => {
    t.equal(gotIH, infoHash, 'initiator received correct infoHash')
    t.equal(gotPI, peerIdB, 'initiator received correct peerId')
  })

  wireB.once('handshake', (gotIH, gotPI) => {
    t.equal(gotIH, infoHash, 'responder received correct infoHash')
    t.equal(gotPI, peerIdA, 'responder received correct peerId')
  })

  wireA.startEncryption(infoHash)
})

test('PE: encrypted message exchange', t => {
  t.plan(4)

  const infoHash = arr2hex(randomBytes(20))
  const peerIdA = arr2hex(randomBytes(20))
  const peerIdB = arr2hex(randomBytes(20))

  const wireA = new Wire('tcpOutgoing', 0, true)
  const wireB = new Wire('tcpIncoming', 0, true)

  linkWires(wireA, wireB)

  wireB.once('crypto-infohash', () => wireB.setInfoHash(infoHash).then(() => {}))

  wireA.once('crypto-handshake', () => {
    wireA.handshake(infoHash, peerIdA, { dht: false, fast: true })
  })
  wireB.once('crypto-handshake', () => {
    wireB.handshake(infoHash, peerIdB, { dht: false, fast: true })
  })

  let gotHandshake = 0
  function onHandshake () {
    gotHandshake++
    if (gotHandshake < 2) return
    wireA.keepAlive()
    wireB.once('keep-alive', () => t.pass('wireB received keep-alive over encrypted channel'))
    wireB.keepAlive()
    wireA.once('keep-alive', () => t.pass('wireA received keep-alive over encrypted channel'))
  }
  wireA.once('handshake', (gotIH, gotPI) => {
    t.equal(gotIH, infoHash, 'initiator received correct infoHash')
    t.equal(gotPI, peerIdB, 'initiator received correct peerId')
    onHandshake()
  })
  wireB.once('handshake', onHandshake)

  wireA.startEncryption(infoHash)
})

test('PE: crypto-infohash correct hash', t => {
  t.plan(3)

  const infoHash = arr2hex(randomBytes(20))
  const expectedHashHash = arr2hex(crypto.createHash('sha1').update(concat([text2arr('req2'), hex2arr(infoHash)])).digest())

  const wireA = new Wire('tcpOutgoing', 0, true)
  const wireB = new Wire('tcpIncoming', 0, true)

  linkWires(wireA, wireB)

  wireB.once('crypto-infohash', ih => {
    t.equal(ih, expectedHashHash, 'crypto-infohash matches HASH(\'req2\', SKEY)')
    wireB.setInfoHash(infoHash).then(() => {})
  })

  wireA.once('crypto-handshake', () => t.pass('handshake completed'))
  wireB.once('crypto-handshake', () => t.pass('handshake completed'))

  wireA.startEncryption(infoHash)
})

test('PE: fallback without protocol encryption', t => {
  t.plan(4)

  const infoHash = arr2hex(randomBytes(20))
  const peerIdA = arr2hex(randomBytes(20))
  const peerIdB = arr2hex(randomBytes(20))

  const wireA = new Wire('tcpOutgoing', 0, false)
  const wireB = new Wire('tcpIncoming', 0, false)

  linkWires(wireA, wireB)

  wireB.once('handshake', () => wireB.handshake(infoHash, peerIdB))
  wireA.once('handshake', (ih, pid) => {
    t.equal(ih, infoHash, 'initiator received handshake')
    t.equal(pid, peerIdB, 'initiator received correct peerId')
    t.equal(wireA._peState, 'idle', 'initiator peState stayed idle (no PE)')
    t.notOk(wireA._encryptor, 'initiator has no encryptor without PE')
  })

  wireA.handshake(infoHash, peerIdA)
})

test('PE: retries > 0 bypasses PE', t => {
  t.plan(1)

  const infoHash = arr2hex(randomBytes(20))
  const peerIdA = arr2hex(randomBytes(20))
  const peerIdB = arr2hex(randomBytes(20))

  const wireA = new Wire('tcpOutgoing', 1, true)
  const wireB = new Wire('tcpIncoming', 0, false)

  linkWires(wireA, wireB)

  wireB.once('handshake', () => wireB.handshake(infoHash, peerIdB))
  wireA.once('handshake', () => t.pass('handshake succeeded without PE due to retries > 0'))

  wireA.handshake(infoHash, peerIdA)
})

const MESSAGE_PROTOCOL = text2arr('\u0013BitTorrent protocol')

test('PE: MessageStreamEncryptor key exchange and encrypt/decrypt', async t => {
  const infoHash = arr2hex(randomBytes(20))
  const wire = new Wire('tcpOutgoing', 0, true)
  wire.startEncryption(infoHash)

  const initEnc = new MessageStreamEncryptor(infoHash)
  const respEnc = new MessageStreamEncryptor(infoHash)

  const step1 = initEnc.generateStepA1()
  t.ok(step1.length >= 96, 'step1 (Ya + padA) >= 96 bytes')

  respEnc.handleStepB1(step1)
  const step2 = respEnc.generateStepB2()
  t.ok(step2.length >= 96, 'step2 (Yb + padB) >= 96 bytes')
  t.ok(respEnc.S, 'responder computed shared secret S')
  t.ok(respEnc.dh, 'responder has DH keys')

  await initEnc.handleStepA2(step2)
  t.ok(initEnc.S, 'initiator computed shared secret S')
  t.ok(initEnc.encryptCipher, 'initiator initialized encrypt cipher')
  t.ok(initEnc.decryptCipher, 'initiator initialized decrypt cipher')

  const step3 = await initEnc.generateStepA3()
  t.ok(step3.length >= 40, 'step3 (req1 + xor + encrypted) >= 40 bytes')

  respEnc.skeyHex = infoHash
  await respEnc._initializeCiphers('B')

  const result = await respEnc.handleStepB3(step3)
  t.ok(result, 'responder successfully processed step3')
  t.equal(typeof result.infoHashHash, 'string', 'infoHashHash is a hex string')
  t.equal(result.infoHashHash.length, 40, 'infoHashHash is 40 hex chars')

  const step4 = respEnc.generateStepB4()
  t.ok(step4.length >= 14, 'step4 (encrypted VC + select + len(padD) + padD) >= 14 bytes')

  const padDLen = initEnc.handleStepA4(step4)
  t.equal(typeof padDLen, 'number', 'initiator processed step4, got padD length')
  t.ok(initEnc._isEncrypted, 'initiator marked encrypted after step4')

  const plaintext = new Uint8Array([1, 2, 3, 4, 5])
  const encrypted = respEnc.encrypt(plaintext)
  t.notOk(equal(encrypted, plaintext), 'encrypted data differs from plaintext')
  const decrypted = initEnc.decrypt(encrypted)
  t.ok(equal(decrypted, plaintext), 'decrypted data matches original plaintext')

  t.end()
})

test('PE: handshake embedded in IA payload', async t => {
  const infoHash = arr2hex(randomBytes(20))
  const peerId = arr2hex(randomBytes(20))
  const infoHashBytes = hex2arr(infoHash)
  const peerIdBytes = hex2arr(peerId)

  const wire = new Wire('tcpOutgoing', 0, true)
  wire.startEncryption(infoHash)

  const initEnc = new MessageStreamEncryptor(infoHash)
  const respEnc = new MessageStreamEncryptor(infoHash)

  const step1 = initEnc.generateStepA1()
  respEnc.handleStepB1(step1)
  const step2 = respEnc.generateStepB2()
  await initEnc.handleStepA2(step2)

  const btHandshake = concat([
    MESSAGE_PROTOCOL,
    new Uint8Array([0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
    infoHashBytes,
    peerIdBytes
  ])

  const step3 = await initEnc.generateStepA3(btHandshake)

  respEnc.skeyHex = infoHash
  await respEnc._initializeCiphers('B')

  const result = await respEnc.handleStepB3(step3)
  t.ok(result, 'responder processed step3 with IA')
  t.ok(result.ia.length > 0, 'IA payload is non-empty')
  t.equal(result.ia[0], 19, 'IA starts with pstrlen=19')
  t.equal(arr2text(result.ia.slice(1, 20)), 'BitTorrent protocol', 'IA contains BT handshake protocol')
  t.equal(arr2hex(result.ia.slice(28, 48)), infoHash, 'IA contains correct infoHash')
  t.equal(arr2hex(result.ia.slice(48, 68)), peerId, 'IA contains correct peerId')

  t.end()
})
