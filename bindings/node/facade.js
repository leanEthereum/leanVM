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

Aggregate.fromBytes = function fromBytes(data, { xmss = [], sphincs = [] } = {}) {
  return native.aggregateFromBytes(data, xmss, sphincs)
}

function aggregate({ children = [], xmss = [], sphincs = [] } = {}) {
  return native.aggregate(children, xmss, sphincs)
}

module.exports = {
  setup: native.setup,
  XmssSecretKey,
  xmssVerify: native.xmssVerify,
  SphincsSecretKey,
  sphincsVerify: native.sphincsVerify,
  VrfKey,
  vrfVerify: native.vrfVerify,
  Aggregate,
  aggregate,
}
