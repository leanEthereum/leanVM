## Nim bindings for leanXMSS and leanSPHINCS signatures, their recursive aggregation, and a VRF.
##
## - **leanXMSS** is stateful: a key signs at `2^32` leaf indices, and must never sign two
##   different messages at the same leaf index.
## - **leanSPHINCS** is stateless: a key signs at most `2^30` messages; signing is deterministic.
## - **VRF** is the consensus `pq` feature's VRF tree, pruned to the slots a validator proposes in.
##
## Public keys and messages are 32 bytes; signatures are fixed-size byte arrays. Fallible calls
## return `Result[T, string]` and never raise; verification returns `bool`.
##
## `XmssSecretKey`, `SphincsSecretKey`, `VrfKey` and `LeanPqAggregate` are
## references to native handles. The garbage collector frees a handle once nothing refers to it;
## `close` frees it at once, after which every call on that value returns an error. Do not `close`
## a value while another thread uses it.

{.push raises: [], gcsafe.}

import
  results,
  ./lean_pq/abi

export results

const
  LeanPqMessageLen* = 32
  LeanPqPublicKeyLen* = 32
  LeanPqSeedLen* = 32
  XmssSecretKeyLen* = 32
  XmssSignatureLen* = 2404
  SphincsSecretKeyLen* = 32
  SphincsSignatureLen* = 7740
  VrfRootLen* = 32
  VrfProofLen* = 1024
    ## The slot's secret, then its leaf's 31 siblings.
  MaxAggregateChildren* = 16
    ## The most child aggregates one `LeanPqAggregate.init` call accepts.

type
  LeanPqMessage* = array[LeanPqMessageLen, byte]
  LeanPqSeed* = array[LeanPqSeedLen, byte]
  XmssPublicKey* = array[LeanPqPublicKeyLen, byte]
  XmssSignature* = array[XmssSignatureLen, byte]
  SphincsPublicKey* = array[LeanPqPublicKeyLen, byte]
  SphincsSignature* = array[SphincsSignatureLen, byte]
  VrfRoot* = array[VrfRootLen, byte]
  VrfProof* = array[VrfProofLen, byte]

  XmssSignedMessage* = object
    ## A raw leanXMSS signature input to `LeanPqAggregate.init`.
    publicKey*: XmssPublicKey
    message*: LeanPqMessage
    signature*: XmssSignature

  SphincsSignedMessage* = object
    ## A raw leanSPHINCS signature input to `LeanPqAggregate.init`.
    publicKey*: SphincsPublicKey
    message*: LeanPqMessage
    signature*: SphincsSignature

  LeanPqClaim* = object
    ## A `(public key, message)` pair an aggregate attests.
    publicKey*: array[LeanPqPublicKeyLen, byte]
    message*: LeanPqMessage

  XmssSecretKeyObj = object
    handle: ptr LpqXmssSecretKey

  XmssSecretKey* = ref XmssSecretKeyObj
    ## A stateful leanXMSS secret key. Never sign two different messages at the same leaf index.

  SphincsSecretKeyObj = object
    handle: ptr LpqSphincsSecretKey

  SphincsSecretKey* = ref SphincsSecretKeyObj
    ## A stateless leanSPHINCS secret key.

  VrfKeyObj = object
    handle: ptr LpqVrfKey

  VrfKey* = ref VrfKeyObj
    ## A VRF key: a seed and its slots, which fix the root, so keep both.

  LeanPqAggregateObj = object
    handle: ptr LpqAggregate

  LeanPqAggregate* = ref LeanPqAggregateObj
    ## A verified proof that each listed public key signed its message.

# The native records are these objects' bytes, so slices of them pass to the bridge as they are.
static:
  doAssert sizeof(XmssSignedMessage) == 2468
  doAssert sizeof(SphincsSignedMessage) == 7804
  doAssert sizeof(LeanPqClaim) == 64

# The `var` parameter is the hook signature both `--mm:refc` and `--mm:orc` accept.
proc `=destroy`(key: var XmssSecretKeyObj) =
  if not key.handle.isNil:
    lpqXmssSecretKeyDestroy(key.handle)
    key.handle = nil

proc `=destroy`(key: var SphincsSecretKeyObj) =
  if not key.handle.isNil:
    lpqSphincsSecretKeyDestroy(key.handle)
    key.handle = nil

proc `=destroy`(key: var VrfKeyObj) =
  if not key.handle.isNil:
    lpqVrfKeyDestroy(key.handle)
    key.handle = nil

proc `=destroy`(aggregate: var LeanPqAggregateObj) =
  if not aggregate.handle.isNil:
    lpqAggregateDestroy(aggregate.handle)
    aggregate.handle = nil

proc `=copy`(dest: var XmssSecretKeyObj, source: XmssSecretKeyObj) {.error.}
proc `=copy`(dest: var SphincsSecretKeyObj, source: SphincsSecretKeyObj) {.error.}
proc `=copy`(dest: var VrfKeyObj, source: VrfKeyObj) {.error.}
proc `=copy`(dest: var LeanPqAggregateObj, source: LeanPqAggregateObj) {.error.}

##############################################################
# Private helpers
##############################################################

func bytesPtr(data: openArray[byte]): ptr byte =
  if data.len == 0: nil else: addr data[0]

proc freeBuffer(buffer: LpqBuffer) =
  if not buffer.data.isNil:
    lpqBufferFree(buffer.data, buffer.len)

proc nativeError(status: int32): string =
  let fallback = "native lean-pq operation failed with status " & $status
  var buffer: LpqBuffer
  if lpqLastError(addr buffer) != LpqOk:
    return fallback
  defer: freeBuffer(buffer)
  if buffer.data.isNil or buffer.len == 0:
    return fallback
  var message = newString(int(buffer.len))
  copyMem(addr message[0], buffer.data, int(buffer.len))
  message

proc check(status: int32): Result[void, string] =
  if status == LpqOk:
    ok()
  else:
    err(nativeError(status))

proc takeBytes(buffer: LpqBuffer): Result[seq[byte], string] =
  defer: freeBuffer(buffer)
  if buffer.len == 0:
    return ok(newSeq[byte]())
  if buffer.data.isNil:
    return err("native buffer is null")
  var bytes = newSeqUninit[byte](int(buffer.len))
  copyMem(addr bytes[0], buffer.data, int(buffer.len))
  ok(bytes)

proc takeArray[N: static int](buffer: LpqBuffer, kind: string): Result[array[N, byte], string] =
  defer: freeBuffer(buffer)
  if buffer.data.isNil or int(buffer.len) != N:
    return err("native " & kind & " has " & $buffer.len & " bytes, expected " & $N)
  var output {.noinit.}: array[N, byte]
  copyMem(addr output[0], buffer.data, N)
  ok(output)

proc takeClaims(buffer: LpqBuffer): Result[seq[LeanPqClaim], string] =
  let bytes = ? takeBytes(buffer)
  if bytes.len mod sizeof(LeanPqClaim) != 0:
    return err("native claim data is not a multiple of " & $sizeof(LeanPqClaim) & " bytes")
  var claims = newSeq[LeanPqClaim](bytes.len div sizeof(LeanPqClaim))
  if claims.len > 0:
    copyMem(addr claims[0], addr bytes[0], bytes.len)
  ok(claims)

func nativeHandle(key: XmssSecretKey): Result[ptr LpqXmssSecretKey, string] =
  if key.isNil or key.handle.isNil:
    err("leanXMSS secret key is closed")
  else:
    ok(key.handle)

func nativeHandle(key: SphincsSecretKey): Result[ptr LpqSphincsSecretKey, string] =
  if key.isNil or key.handle.isNil:
    err("leanSPHINCS secret key is closed")
  else:
    ok(key.handle)

func nativeHandle(key: VrfKey): Result[ptr LpqVrfKey, string] =
  if key.isNil or key.handle.isNil:
    err("VRF key is closed")
  else:
    ok(key.handle)

func nativeHandle(aggregate: LeanPqAggregate): Result[ptr LpqAggregate, string] =
  if aggregate.isNil or aggregate.handle.isNil:
    err("aggregate is closed")
  else:
    ok(aggregate.handle)

##############################################################
# leanXMSS
##############################################################

proc generate*(T: type XmssSecretKey): Result[XmssSecretKey, string] =
  ## A fresh key from the operating system's randomness.
  var handle: ptr LpqXmssSecretKey
  ? check(lpqXmssSecretKeyGenerate(addr handle))
  if handle.isNil:
    return err("native leanXMSS secret key is null")
  ok(XmssSecretKey(handle: handle))

proc fromBytes*(T: type XmssSecretKey, bytes: openArray[byte]): Result[XmssSecretKey, string] =
  ## Restores a key from `toBytes`: its 32-byte seed.
  var handle: ptr LpqXmssSecretKey
  ? check(lpqXmssSecretKeyFromBytes(bytesPtr(bytes), csize_t(bytes.len), addr handle))
  if handle.isNil:
    return err("native leanXMSS secret key is null")
  ok(XmssSecretKey(handle: handle))

proc fromSeed*(T: type XmssSecretKey, seed: LeanPqSeed): Result[XmssSecretKey, string] =
  ## The seed is the key's entire secret material: never derive another key from it.
  XmssSecretKey.fromBytes(seed)

proc fromCacheBytes*(
    T: type XmssSecretKey, seed: LeanPqSeed, publicKey: XmssPublicKey, cache: openArray[byte]
): Result[XmssSecretKey, string] =
  ## Loads a key from its seed, its public key and the bytes of `cacheToBytes`, building no
  ## tree. The cache is checked against the public key.
  var handle: ptr LpqXmssSecretKey
  ? check(lpqXmssSecretKeyFromCacheBytes(
    bytesPtr(seed), csize_t(seed.len),
    bytesPtr(publicKey), csize_t(publicKey.len),
    bytesPtr(cache), csize_t(cache.len), addr handle))
  if handle.isNil:
    return err("native leanXMSS secret key is null")
  ok(XmssSecretKey(handle: handle))

proc toBytes*(key: XmssSecretKey): Result[array[XmssSecretKeyLen, byte], string] =
  ## SECRET KEY MATERIAL: the 32-byte seed.
  let handle = ? key.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqXmssSecretKeyToBytes(handle, addr buffer))
  takeArray[XmssSecretKeyLen](buffer, "leanXMSS secret key")

proc cacheToBytes*(key: XmssSecretKey): Result[seq[byte], string] =
  ## The trees the key holds, without any secret.
  let handle = ? key.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqXmssSecretKeyCacheToBytes(handle, addr buffer))
  takeBytes(buffer)

proc publicKey*(key: XmssSecretKey): Result[XmssPublicKey, string] =
  let handle = ? key.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqXmssSecretKeyPublicKey(handle, addr buffer))
  takeArray[LeanPqPublicKeyLen](buffer, "leanXMSS public key")

proc prepare*(key: XmssSecretKey, leafIndex: uint32): Result[void, string] =
  ## Builds the bottom tree `leafIndex` falls in ahead of signing there.
  let handle = ? key.nativeHandle()
  check(lpqXmssSecretKeyPrepare(handle, leafIndex))

proc sign*(
    key: XmssSecretKey, message: LeanPqMessage, leafIndex: uint32
): Result[XmssSignature, string] =
  ## Never sign two different messages at the same `leafIndex`.
  let handle = ? key.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqXmssSecretKeySign(
    handle, addr message[0], csize_t(message.len), leafIndex, addr buffer))
  takeArray[XmssSignatureLen](buffer, "leanXMSS signature")

proc close*(key: XmssSecretKey) =
  ## Frees the native key now. Safe to call more than once.
  if not key.isNil and not key.handle.isNil:
    lpqXmssSecretKeyDestroy(key.handle)
    key.handle = nil

proc xmssVerify*(
    publicKey: XmssPublicKey, message: LeanPqMessage, signature: XmssSignature
): bool =
  ## Whether `signature` is `publicKey`'s leanXMSS signature of `message`.
  lpqXmssVerify(
    addr publicKey[0], csize_t(publicKey.len),
    addr message[0], csize_t(message.len),
    addr signature[0], csize_t(signature.len)) == LpqOk

##############################################################
# leanSPHINCS
##############################################################

proc generate*(T: type SphincsSecretKey): Result[SphincsSecretKey, string] =
  ## A fresh key from the operating system's randomness.
  var handle: ptr LpqSphincsSecretKey
  ? check(lpqSphincsSecretKeyGenerate(addr handle))
  if handle.isNil:
    return err("native leanSPHINCS secret key is null")
  ok(SphincsSecretKey(handle: handle))

proc fromSeed*(T: type SphincsSecretKey, seed: LeanPqSeed): Result[SphincsSecretKey, string] =
  ## The seed is the key's entire secret material: never derive another key from it.
  var handle: ptr LpqSphincsSecretKey
  ? check(lpqSphincsSecretKeyFromSeed(addr seed[0], csize_t(seed.len), addr handle))
  if handle.isNil:
    return err("native leanSPHINCS secret key is null")
  ok(SphincsSecretKey(handle: handle))

proc fromBytes*(
    T: type SphincsSecretKey, bytes: openArray[byte]
): Result[SphincsSecretKey, string] =
  ## Restores a key from `toBytes`: its 32-byte seed.
  var handle: ptr LpqSphincsSecretKey
  ? check(lpqSphincsSecretKeyFromBytes(bytesPtr(bytes), csize_t(bytes.len), addr handle))
  if handle.isNil:
    return err("native leanSPHINCS secret key is null")
  ok(SphincsSecretKey(handle: handle))

proc toBytes*(key: SphincsSecretKey): Result[array[SphincsSecretKeyLen, byte], string] =
  ## SECRET KEY MATERIAL: the 32-byte seed.
  let handle = ? key.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqSphincsSecretKeyToBytes(handle, addr buffer))
  takeArray[SphincsSecretKeyLen](buffer, "leanSPHINCS secret key")

proc publicKey*(key: SphincsSecretKey): Result[SphincsPublicKey, string] =
  let handle = ? key.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqSphincsSecretKeyPublicKey(handle, addr buffer))
  takeArray[LeanPqPublicKeyLen](buffer, "leanSPHINCS public key")

proc sign*(key: SphincsSecretKey, message: LeanPqMessage): Result[SphincsSignature, string] =
  let handle = ? key.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqSphincsSecretKeySign(handle, addr message[0], csize_t(message.len), addr buffer))
  takeArray[SphincsSignatureLen](buffer, "leanSPHINCS signature")

proc close*(key: SphincsSecretKey) =
  ## Frees the native key now. Safe to call more than once.
  if not key.isNil and not key.handle.isNil:
    lpqSphincsSecretKeyDestroy(key.handle)
    key.handle = nil

proc sphincsVerify*(
    publicKey: SphincsPublicKey, message: LeanPqMessage, signature: SphincsSignature
): bool =
  ## Whether `signature` is `publicKey`'s leanSPHINCS signature of `message`.
  lpqSphincsVerify(
    addr publicKey[0], csize_t(publicKey.len),
    addr message[0], csize_t(message.len),
    addr signature[0], csize_t(signature.len)) == LpqOk

##############################################################
# VRF
##############################################################

proc init*(T: type VrfKey, seed: LeanPqSeed, start, stop: uint32): Result[VrfKey, string] =
  ## Builds the key of the slots `start ..< stop`, hashing every slot. Fails if the range is empty
  ## or ends past `2^31`.
  var handle: ptr LpqVrfKey
  ? check(lpqVrfKeyNew(addr seed[0], csize_t(seed.len), start, stop, addr handle))
  if handle.isNil:
    return err("native VRF key is null")
  ok(VrfKey(handle: handle))

proc fromCacheBytes*(
    T: type VrfKey, seed: LeanPqSeed, root: VrfRoot, cache: openArray[byte]
): Result[VrfKey, string] =
  ## Rebuilds a key from its seed, its root and a cache from `cacheToBytes`, without hashing the
  ## range. Fails if the cache is malformed or does not lead to `root`.
  var handle: ptr LpqVrfKey
  ? check(lpqVrfKeyFromCacheBytes(
    addr seed[0], csize_t(seed.len), addr root[0], csize_t(root.len),
    bytesPtr(cache), csize_t(cache.len), addr handle))
  if handle.isNil:
    return err("native VRF key is null")
  ok(VrfKey(handle: handle))

proc cacheToBytes*(key: VrfKey): Result[seq[byte], string] =
  ## Encodes the key's cache: its range and cached layer, no secret.
  let handle = ? key.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqVrfKeyCacheToBytes(handle, addr buffer))
  takeBytes(buffer)

proc root*(key: VrfKey): Result[VrfRoot, string] =
  let handle = ? key.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqVrfKeyRoot(handle, addr buffer))
  takeArray[VrfRootLen](buffer, "VRF root")

proc proof*(key: VrfKey, slot: uint32): Result[VrfProof, string] =
  ## The proof of `slot`. Fails outside the range.
  let handle = ? key.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqVrfKeyProof(handle, slot, addr buffer))
  takeArray[VrfProofLen](buffer, "VRF proof")

proc close*(key: VrfKey) =
  ## Frees the native key now. Safe to call more than once.
  if not key.isNil and not key.handle.isNil:
    lpqVrfKeyDestroy(key.handle)
    key.handle = nil

proc vrfVerify*(root: VrfRoot, slot: uint64, proof: VrfProof): bool =
  ## Whether `proof` opens `slot` under `root`.
  lpqVrfVerify(
    addr root[0], csize_t(root.len), slot, addr proof[0], csize_t(proof.len)) == LpqOk

##############################################################
# Aggregation
##############################################################

proc leanPqSetup*(threads: int): Result[void, string] =
  ## Starts the prover on `threads` threads (0: one per core). Fails if the prover already runs
  ## with another count.
  if threads < 0:
    return err("threads must not be negative")
  check(lpqSetup(csize_t(threads)))

proc create(
    children: openArray[LeanPqAggregate],
    xmss: openArray[XmssSignedMessage],
    sphincs: openArray[SphincsSignedMessage],
    only: bool,
    xmssClaims: openArray[LeanPqClaim] = [],
    sphincsClaims: openArray[LeanPqClaim] = [],
): Result[LeanPqAggregate, string] =
  if children.len > MaxAggregateChildren:
    return err("at most " & $MaxAggregateChildren & " child aggregates, got " & $children.len)
  var handles: array[MaxAggregateChildren, ptr LpqAggregate]
  for index, child in children:
    handles[index] = ? child.nativeHandle()

  let
    childrenPtr = if children.len == 0: nil else: addr handles[0]
    xmssPtr = if xmss.len == 0: nil else: cast[ptr byte](addr xmss[0])
    sphincsPtr = if sphincs.len == 0: nil else: cast[ptr byte](addr sphincs[0])
    xmssClaimsPtr = if xmssClaims.len == 0: nil else: cast[ptr byte](addr xmssClaims[0])
    sphincsClaimsPtr = if sphincsClaims.len == 0: nil else: cast[ptr byte](addr sphincsClaims[0])
  var handle: ptr LpqAggregate
  if only:
    ? check(lpqAggregateCreateOnly(
      childrenPtr, csize_t(children.len),
      xmssPtr, csize_t(xmss.len),
      sphincsPtr, csize_t(sphincs.len),
      xmssClaimsPtr, csize_t(xmssClaims.len),
      sphincsClaimsPtr, csize_t(sphincsClaims.len),
      addr handle))
  else:
    ? check(lpqAggregateCreate(
      childrenPtr, csize_t(children.len),
      xmssPtr, csize_t(xmss.len),
      sphincsPtr, csize_t(sphincs.len),
      addr handle))
  if handle.isNil:
    return err("native aggregate is null")
  ok(LeanPqAggregate(handle: handle))

proc init*(
    T: type LeanPqAggregate,
    children: openArray[LeanPqAggregate] = [],
    xmss: openArray[XmssSignedMessage] = [],
    sphincs: openArray[SphincsSignedMessage] = [],
): Result[LeanPqAggregate, string] =
  ## Verifies the raw signatures, then proves the union of their claims and the children's. At
  ## least one input is required. Children are neither consumed nor closed.
  create(children, xmss, sphincs, only = false)

proc initOnly*(
    T: type LeanPqAggregate,
    children: openArray[LeanPqAggregate] = [],
    xmss: openArray[XmssSignedMessage] = [],
    sphincs: openArray[SphincsSignedMessage] = [],
    xmssClaims: openArray[LeanPqClaim] = [],
    sphincsClaims: openArray[LeanPqClaim] = [],
): Result[LeanPqAggregate, string] =
  ## `init`, but the result proves exactly `xmssClaims` and `sphincsClaims`, in any order, a
  ## repeat counting once; each must be one the inputs cover.
  create(children, xmss, sphincs, only = true, xmssClaims, sphincsClaims)

proc fromBytes*(
    T: type LeanPqAggregate,
    bytes: openArray[byte],
    xmssClaims: openArray[LeanPqClaim] = [],
    sphincsClaims: openArray[LeanPqClaim] = [],
): Result[LeanPqAggregate, string] =
  ## Verifies that a proof from `toBytes` proves exactly `xmssClaims` and `sphincsClaims`, in any
  ## order, a repeated claim counting once. The encoding holds no claims: send them alongside the
  ## proof or rebuild them on the receiving side. Every `LeanPqAggregate` is proven.
  let
    xmssPtr = if xmssClaims.len == 0: nil else: cast[ptr byte](addr xmssClaims[0])
    sphincsPtr = if sphincsClaims.len == 0: nil else: cast[ptr byte](addr sphincsClaims[0])
  var handle: ptr LpqAggregate
  ? check(lpqAggregateFromBytes(
    bytesPtr(bytes), csize_t(bytes.len),
    xmssPtr, csize_t(xmssClaims.len),
    sphincsPtr, csize_t(sphincsClaims.len),
    addr handle))
  if handle.isNil:
    return err("native aggregate is null")
  ok(LeanPqAggregate(handle: handle))

proc toBytes*(aggregate: LeanPqAggregate): Result[seq[byte], string] =
  ## The proof alone, without its claims.
  let handle = ? aggregate.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqAggregateToBytes(handle, addr buffer))
  takeBytes(buffer)

proc xmssClaims*(aggregate: LeanPqAggregate): Result[seq[LeanPqClaim], string] =
  ## The leanXMSS claims, strictly sorted by public key, then message.
  let handle = ? aggregate.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqAggregateXmssClaims(handle, addr buffer))
  takeClaims(buffer)

proc sphincsClaims*(aggregate: LeanPqAggregate): Result[seq[LeanPqClaim], string] =
  ## The leanSPHINCS claims, strictly sorted by public key, then message.
  let handle = ? aggregate.nativeHandle()
  var buffer: LpqBuffer
  ? check(lpqAggregateSphincsClaims(handle, addr buffer))
  takeClaims(buffer)

proc close*(aggregate: LeanPqAggregate) =
  ## Frees the native aggregate now. Safe to call more than once.
  if not aggregate.isNil and not aggregate.handle.isNil:
    lpqAggregateDestroy(aggregate.handle)
    aggregate.handle = nil
