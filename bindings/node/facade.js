const native = require('./index.js')

const { Aggregate, Sidecar, SphincsSecretKey, XmssSecretKey } = native

XmssSecretKey.generate = native.generateXmssSecretKey
XmssSecretKey.fromSeed = native.xmssSecretKeyFromSeed
XmssSecretKey.fromBytes = native.xmssSecretKeyFromBytes

SphincsSecretKey.generate = native.generateSphincsSecretKey
SphincsSecretKey.fromSeed = native.sphincsSecretKeyFromSeed
SphincsSecretKey.fromBytes = native.sphincsSecretKeyFromBytes

Sidecar.connect = native.sidecarConnect
Sidecar.start = native.sidecarStart
Sidecar.prototype.aggregate = function aggregate({ children = [], xmss = [], sphincs = [] } = {}) {
  return this.prove(children, xmss, sphincs)
}
Sidecar.prototype.verify = function verify(data, { xmss = [], sphincs = [] } = {}) {
  return this.check(data, xmss, sphincs)
}

module.exports = {
  XmssSecretKey,
  xmssVerify: native.xmssVerify,
  SphincsSecretKey,
  sphincsVerify: native.sphincsVerify,
  Aggregate,
  Sidecar,
}
