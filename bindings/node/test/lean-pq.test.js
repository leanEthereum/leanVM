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

  const loaded = await lpq.XmssSecretKey.fromCacheBytes(seed(7), cache)
  assert.deepEqual(loaded.publicKey, key.publicKey)
  assert.deepEqual(loaded.cacheToBytes(), cache)
  const signature = await loaded.sign(message, 3)
  assert.deepEqual(signature, await key.sign(message, 3))
  lpq.xmssVerify(key.publicKey, message, signature)

  await assert.rejects(lpq.XmssSecretKey.fromCacheBytes(seed(7), cache.subarray(1)), /tree cache has an invalid length/)
})

test('aggregates both schemes recursively', async () => {
  const first = Buffer.alloc(32, 0x11)
  const second = Buffer.alloc(32, 0x22)
  const xmssKey = await lpq.XmssSecretKey.fromSeed(seed(5))
  const sphincsKey = await lpq.SphincsSecretKey.fromSeed(seed(6))

  const left = await lpq.aggregate({
    xmss: [{ publicKey: xmssKey.publicKey, message: first, signature: await xmssKey.sign(first, 0) }],
  })
  const right = await lpq.aggregate({
    sphincs: [{ publicKey: sphincsKey.publicKey, message: first, signature: await sphincsKey.sign(first) }],
  })
  const root = await lpq.aggregate({
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
  const received = await lpq.Aggregate.fromBytes(proof, { xmss: xmssClaims, sphincs: sphincsClaims })
  assert.deepEqual(received.xmssClaims, xmssClaims)
  assert.deepEqual(received.sphincsClaims, sphincsClaims)
  assert.deepEqual(received.toBytes(), proof)

  // Claims may come in any order, and a repeated claim counts once.
  const reordered = await lpq.Aggregate.fromBytes(proof, {
    xmss: [xmssClaims[1], xmssClaims[0], xmssClaims[1]],
    sphincs: sphincsClaims,
  })
  assert.deepEqual(reordered.xmssClaims, xmssClaims)

  const rejected = /does not prove the given claims/
  await assert.rejects(lpq.Aggregate.fromBytes(proof, { xmss: xmssClaims }), rejected)
  await assert.rejects(lpq.Aggregate.fromBytes(proof, { xmss: xmssClaims.slice(1), sphincs: sphincsClaims }), rejected)
  await assert.rejects(
    lpq.Aggregate.fromBytes(proof, {
      xmss: xmssClaims,
      sphincs: [{ publicKey: sphincsKey.publicKey, message: second }],
    }),
    rejected,
  )

  const tampered = Buffer.from(proof)
  tampered[tampered.length - 1] ^= 1
  await assert.rejects(lpq.Aggregate.fromBytes(tampered, { xmss: xmssClaims, sphincs: sphincsClaims }))
  await assert.rejects(
    lpq.Aggregate.fromBytes(proof.subarray(0, proof.length - 1), { xmss: xmssClaims, sphincs: sphincsClaims }),
    /malformed aggregate/,
  )
})
