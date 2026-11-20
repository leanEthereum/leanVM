const native = require('./index.js')

const { Aggregate, Sidecar, SphincsSecretKey, VrfKey, XmssSecretKey } = native

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
  VrfKey,
  vrfVerify: native.vrfVerify,
  Aggregate,
  Sidecar,
}
