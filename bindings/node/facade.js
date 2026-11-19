const native = require('./index.js')

const { Aggregate, Sidecar, SphincsSecretKey, XmssSecretKey } = native

XmssSecretKey.generate = native.generateXmssSecretKey
XmssSecretKey.fromSeed = native.xmssSecretKeyFromSeed
XmssSecretKey.fromBytes = native.xmssSecretKeyFromBytes

SphincsSecretKey.generate = native.generateSphincsSecretKey
SphincsSecretKey.fromSeed = native.sphincsSecretKeyFromSeed
SphincsSecretKey.fromBytes = native.sphincsSecretKeyFromBytes

// async: an invalid argument rejects the promise rather than throwing.
Sidecar.connect = async (socket) => native.sidecarConnect(socket)
Sidecar.start = async (binary, socket, threads) => native.sidecarStart(binary, socket, threads)
Sidecar.prototype.aggregate = async function aggregate(input) {
  const { children = [], xmss = [], sphincs = [] } = input ?? {}
  return this.prove(children, xmss, sphincs)
}
Sidecar.prototype.verify = async function verify(data, claims) {
  const { xmss = [], sphincs = [] } = claims ?? {}
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
