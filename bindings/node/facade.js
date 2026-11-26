const native = require('./index.js')

const { Aggregate, SphincsSecretKey, VrfKey, XmssSecretKey } = native

XmssSecretKey.generate = native.generateXmssSecretKey
XmssSecretKey.fromSeed = native.xmssSecretKeyFromSeed
XmssSecretKey.fromBytes = native.xmssSecretKeyFromBytes
XmssSecretKey.fromCacheBytes = native.xmssSecretKeyFromCacheBytes

SphincsSecretKey.generate = native.generateSphincsSecretKey
SphincsSecretKey.fromSeed = native.sphincsSecretKeyFromSeed
SphincsSecretKey.fromBytes = native.sphincsSecretKeyFromBytes

VrfKey.fromSeed = native.vrfKeyFromSeed
VrfKey.fromCacheBytes = native.vrfKeyFromCacheBytes

// async: an invalid argument rejects the promise rather than throwing.
const setup = async (threads) => native.setup(threads)
Aggregate.fromBytes = async function fromBytes(data, claims) {
  const { xmss = [], sphincs = [] } = claims ?? {}
  return native.aggregateFromBytes(data, xmss, sphincs)
}
async function aggregate(input) {
  const { children = [], xmss = [], sphincs = [], only } = input ?? {}
  if (only == null) return native.aggregate(children, xmss, sphincs)
  return native.aggregate(children, xmss, sphincs, only.xmss ?? [], only.sphincs ?? [])
}

module.exports = {
  setup,
  XmssSecretKey,
  xmssVerify: native.xmssVerify,
  SphincsSecretKey,
  sphincsVerify: native.sphincsVerify,
  VrfKey,
  vrfVerify: native.vrfVerify,
  Aggregate,
  aggregate,
}
