const assert = require('node:assert/strict')
const test = require('node:test')

const lpq = require('..')

const seed = (byte) => Buffer.alloc(32, byte)

test('signs and verifies with both schemes', async () => {
  const message = Buffer.alloc(32, 0x42)
  const other = Buffer.alloc(32, 0x43)

  const xmssKey = await lpq.XmssSecretKey.fromSeed(seed(1))
  const xmssSignature = await xmssKey.sign(message, 3)
  assert.equal(xmssSignature.length, 2404)
  lpq.xmssVerify(xmssKey.publicKey, message, xmssSignature)
  assert.throws(() => lpq.xmssVerify(xmssKey.publicKey, other, xmssSignature), /leanXMSS/)

  const sphincsKey = await lpq.SphincsSecretKey.fromSeed(seed(2))
  const sphincsSignature = await sphincsKey.sign(message)
  assert.equal(sphincsSignature.length, 7740)
  lpq.sphincsVerify(sphincsKey.publicKey, message, sphincsSignature)
  assert.throws(() => lpq.sphincsVerify(sphincsKey.publicKey, other, sphincsSignature), /leanSPHINCS/)
})

test('round trips secret keys through bytes', async () => {
  const message = Buffer.alloc(32, 7)

  const xmssKey = await lpq.XmssSecretKey.fromSeed(seed(3))
  const xmssRestored = await lpq.XmssSecretKey.fromBytes(xmssKey.toBytes())
  assert.deepEqual(xmssRestored.publicKey, xmssKey.publicKey)
  lpq.xmssVerify(xmssKey.publicKey, message, await xmssRestored.sign(message, 9))

  const sphincsKey = await lpq.SphincsSecretKey.fromSeed(seed(4))
  const sphincsBytes = sphincsKey.toBytes()
  assert.deepEqual(sphincsBytes, seed(4))
  const sphincsRestored = await lpq.SphincsSecretKey.fromBytes(sphincsBytes)
  assert.deepEqual(sphincsRestored.publicKey, sphincsKey.publicKey)
  lpq.sphincsVerify(sphincsKey.publicKey, message, await sphincsRestored.sign(message))
})

test('loads a leanXMSS key from its tree cache', async () => {
  const message = Buffer.alloc(32, 7)
  const key = await lpq.XmssSecretKey.fromSeed(seed(7))
  await key.prepare(3)
  const cache = key.cacheToBytes()

  const loaded = await lpq.XmssSecretKey.fromCacheBytes(seed(7), key.publicKey, cache)
  assert.deepEqual(loaded.publicKey, key.publicKey)
  assert.deepEqual(loaded.cacheToBytes(), cache)
  const signature = await loaded.sign(message, 3)
  assert.deepEqual(signature, await key.sign(message, 3))
  lpq.xmssVerify(key.publicKey, message, signature)

  // A truncated cache, a tampered one, or another key's is refused.
  const tampered = Buffer.from(cache)
  tampered[0] ^= 1
  const other = (await lpq.XmssSecretKey.fromSeed(seed(8))).publicKey
  for (const [publicKey, bytes] of [[key.publicKey, cache.subarray(1)], [key.publicKey, tampered], [other, cache]]) {
    await assert.rejects(lpq.XmssSecretKey.fromCacheBytes(seed(7), publicKey, bytes), /not this leanXMSS key's tree cache/)
  }
})

const unix = process.platform !== 'win32'
const skip = unix ? false : 'the sidecar needs Unix sockets'

function env(name) {
  const value = process.env[name]
  if (!value) throw new Error(`set ${name} to run the aggregation tests`)
  return value
}

test('aggregates both schemes recursively', { skip }, async () => {
  const sidecar = await lpq.Sidecar.connect(env('LEANVM_SIDECAR_SOCKET'))
  const first = Buffer.alloc(32, 0x11)
  const second = Buffer.alloc(32, 0x22)
  const xmssKey = await lpq.XmssSecretKey.fromSeed(seed(5))
  const sphincsKey = await lpq.SphincsSecretKey.fromSeed(seed(6))

  const left = await sidecar.aggregate({
    xmss: [{ publicKey: xmssKey.publicKey, message: first, signature: await xmssKey.sign(first, 0) }],
  })
  const right = await sidecar.aggregate({
    sphincs: [{ publicKey: sphincsKey.publicKey, message: first, signature: await sphincsKey.sign(first) }],
  })
  const root = await sidecar.aggregate({
    children: [left, right],
    xmss: [{ publicKey: xmssKey.publicKey, message: second, signature: await xmssKey.sign(second, 1) }],
  })

  const xmssClaims = [
    { publicKey: xmssKey.publicKey, message: first },
    { publicKey: xmssKey.publicKey, message: second },
  ]
  const sphincsClaims = [{ publicKey: sphincsKey.publicKey, message: first }]
  assert.deepEqual(root.xmssClaims, xmssClaims)
  assert.deepEqual(root.sphincsClaims, sphincsClaims)

  const proof = root.toBytes()
  const received = await sidecar.verify(proof, { xmss: xmssClaims, sphincs: sphincsClaims })
  assert.deepEqual(received.xmssClaims, xmssClaims)
  assert.deepEqual(received.sphincsClaims, sphincsClaims)
  assert.deepEqual(received.toBytes(), proof)

  // Claims may come in any order, and a repeated claim counts once.
  const reordered = await sidecar.verify(proof, {
    xmss: [xmssClaims[1], xmssClaims[0], xmssClaims[1]],
    sphincs: sphincsClaims,
  })
  assert.deepEqual(reordered.xmssClaims, xmssClaims)

  const rejected = /does not prove the given claims/
  await assert.rejects(sidecar.verify(proof, { xmss: xmssClaims }), rejected)
  await assert.rejects(sidecar.verify(proof, { xmss: xmssClaims.slice(1), sphincs: sphincsClaims }), rejected)
  await assert.rejects(
    sidecar.verify(proof, {
      xmss: xmssClaims,
      sphincs: [{ publicKey: sphincsKey.publicKey, message: second }],
    }),
    rejected,
  )
  const tampered = Buffer.from(proof)
  tampered[tampered.length - 1] ^= 1
  await assert.rejects(sidecar.verify(tampered, { xmss: xmssClaims, sphincs: sphincsClaims }), rejected)
  await assert.rejects(
    sidecar.verify(proof.subarray(0, proof.length - 1), { xmss: xmssClaims, sphincs: sphincsClaims }),
    rejected,
  )
  await assert.rejects(sidecar.aggregate(), /aggregation failed/)
  await sidecar.close()
  await assert.rejects(sidecar.verify(proof, { xmss: xmssClaims, sphincs: sphincsClaims }), /closed/)
})

test('starts and stops its own sidecar', { skip }, async () => {
  const fs = require('node:fs')
  const os = require('node:os')
  const path = require('node:path')
  const shared = await lpq.Sidecar.connect(env('LEANVM_SIDECAR_SOCKET'))
  const key = await lpq.XmssSecretKey.fromSeed(seed(7))
  const message = Buffer.alloc(32, 0x33)
  const proof = await shared.aggregate({
    xmss: [{ publicKey: key.publicKey, message, signature: await key.sign(message, 0) }],
  })
  await shared.close()

  // Short: a Unix socket path holds at most 104 bytes on macOS.
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'lpq'))
  try {
    const socket = path.join(directory, 's.sock')
    await assert.rejects(lpq.Sidecar.start(env('LEANVM_SIDECAR_BIN'), socket, -1), /threads/)
    const started = await lpq.Sidecar.start(env('LEANVM_SIDECAR_BIN'), socket, 2)
    try {
      assert.ok(['experimental', 'stable'].includes(started.prover))
      await started.verify(proof.toBytes(), { xmss: proof.xmssClaims })
    } finally {
      await started.close()
    }
    await assert.rejects(lpq.Sidecar.connect(socket), /leanVM sidecar/)
  } finally {
    fs.rmSync(directory, { recursive: true })
  }
})

test('connecting where no sidecar listens fails', async () => {
  await assert.rejects(lpq.Sidecar.connect('/nonexistent/sidecar.sock'), unix ? /leanVM sidecar/ : /Unix sockets/)
})

test('opens VRF proofs under the root', async () => {
  const key = await lpq.VrfKey.fromSeed(seed(9), 100, 200)
  const root = key.root()
  assert.equal(root.toString('hex'), 'c7e3eaa5a1af5e528e56beb589b4d1c579f5fb8939ddd7f6b1ce2141bc096b45')

  const proof = key.proof(150)
  assert.equal(proof.length, 1024)
  lpq.vrfVerify(root, 150, proof)
  assert.throws(() => lpq.vrfVerify(root, 151, proof), /VRF proof for slot 151/)
  for (const slot of [100, 151, 199]) lpq.vrfVerify(root, slot, key.proof(slot))
})

test('loads a VRF key from its cache', async () => {
  const cache = (await lpq.VrfKey.fromSeed(seed(9), 100, 200)).cacheToBytes()

  const root = Buffer.from('c7e3eaa5a1af5e528e56beb589b4d1c579f5fb8939ddd7f6b1ce2141bc096b45', 'hex')
  const loaded = await lpq.VrfKey.fromCacheBytes(seed(9), root, cache)
  assert.deepEqual(loaded.cacheToBytes(), cache)
  lpq.vrfVerify(root, 150, loaded.proof(150))

  await assert.rejects(lpq.VrfKey.fromCacheBytes(seed(9), root, cache.subarray(0, -1)), /not this VRF key's cache/)
  await assert.rejects(lpq.VrfKey.fromCacheBytes(seed(9), Buffer.alloc(32), cache), /not this VRF key's cache/)
  await assert.rejects(lpq.VrfKey.fromCacheBytes(Buffer.alloc(31), root, cache), /seed must be 32 bytes/)
})

test('rejects VRF slots outside the range and bad encodings', async () => {
  await assert.rejects(lpq.VrfKey.fromSeed(seed(9), 5, 5), /VRF range 5\.\.5/)
  await assert.rejects(lpq.VrfKey.fromSeed(seed(9), 0, 2 ** 31 + 1), /ends past 2\^31/)
  await assert.rejects(lpq.VrfKey.fromSeed(Buffer.alloc(31), 0, 1), /seed must be 32 bytes/)

  const key = await lpq.VrfKey.fromSeed(seed(9), 100, 200)
  assert.throws(() => key.proof(99), /VRF slot 99/)
  assert.throws(() => key.proof(200), /VRF slot 200/)
  assert.throws(() => lpq.vrfVerify(key.root(), 150, key.proof(150).subarray(1)), /proof must be 1024 bytes/)
})
