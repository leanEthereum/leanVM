## Declarations of the internal `lpq_*` bridge ABI and the link flags for its static archive.
##
## The ABI is private to the bindings: it is not a supported C API.
## `include/lean_pq_native.h` documents it and must match `bindings/native/include`.
##
## The archive is `native/<target>/liblean_pq_native.a` inside this package. The first build
## downloads it from this version's GitHub release, which has one for Linux x86_64 and aarch64
## (glibc), macOS (universal) and Windows x86_64 (MinGW); `-d:leanPqNativeUrl=URL` names another
## location of the release's `lean-pq-native-<target>.a` files. Pass `-d:leanPqNativeDir=DIR` to
## link the archive in `DIR` instead, for other targets or builds without network access.

{.push raises: [], gcsafe.}

from std/os import parentDir, `/`, quoteShell, fileExists

const
  leanPqVersion = "0.19.1" # x-release-please-version
  leanPqNativeDir {.strdefine.} = ""
  leanPqNativeUrl {.strdefine, used.} =
    "https://github.com/leanEthereum/leanVM/releases/download/bindings-v" & leanPqVersion
  packageDir = currentSourcePath().parentDir().parentDir()
  lpqHeader = packageDir / "include" / "lean_pq_native.h"

  bundledTarget =
    when defined(linux) and defined(amd64): "x86_64-linux-gnu"
    elif defined(linux) and defined(arm64): "aarch64-linux-gnu"
    elif defined(macosx) and (defined(amd64) or defined(arm64)): "universal-macos"
    elif defined(windows) and defined(amd64) and not defined(vcc): "x86_64-windows-gnu"
    else: ""

when leanPqNativeDir.len == 0 and bundledTarget.len == 0:
  {.error: "lean_pq has no prebuilt native archive for this target; pass -d:leanPqNativeDir=DIR".}

const nativeArchive =
  (when leanPqNativeDir.len > 0: leanPqNativeDir
   else: packageDir / "native" / bundledTarget) / "liblean_pq_native.a"

when leanPqNativeDir.len == 0 and not fileExists(nativeArchive):
  const
    nativeUrl = leanPqNativeUrl & "/lean-pq-native-" & bundledTarget & ".a"
    partial = nativeArchive & ".part"
    # A complete download is renamed into place, so an interrupted one is never linked.
    fetch =
      when defined(windows):
        "cmd /c curl -fsSL --retry 3 --create-dirs -o " & quoteShell(partial) & " " &
          quoteShell(nativeUrl) & " && move /y " & quoteShell(partial) & " " & quoteShell(nativeArchive)
      else:
        "curl -fsSL --retry 3 --create-dirs -o " & quoteShell(partial) & " " & quoteShell(nativeUrl) &
          " && mv " & quoteShell(partial) & " " & quoteShell(nativeArchive)
    fetched = gorgeEx(fetch)
  when fetched.exitCode != 0 or not fileExists(nativeArchive):
    {.error: "lean_pq could not download " & nativeUrl & ": " & fetched.output &
      "; pass -d:leanPqNativeDir=DIR to link a liblean_pq_native.a you built".}

{.passl: quoteShell(nativeArchive).}

# The libraries the Rust standard library links against (`--print native-static-libs`).
when defined(linux):
  {.passl: "-lgcc_s -lutil -lrt -lpthread -lm -ldl".}
elif defined(macosx):
  {.passl: "-lm".}
elif defined(windows):
  # `synchronization` provides WaitOnAddress and WakeByAddressSingle: MinGW ld scans the archive
  # once, and the import stubs Rust embeds for them can come before the objects that call them.
  {.passl: "-lkernel32 -lntdll -luserenv -lws2_32 -ldbghelp -lsynchronization".}

type
  LpqBuffer* {.importc: "lpq_buffer", header: lpqHeader, bycopy.} = object
    data*: ptr byte
    len*: csize_t

  LpqXmssSecretKey* {.importc: "lpq_xmss_secret_key", header: lpqHeader,
    incompleteStruct.} = object
  LpqSphincsSecretKey* {.importc: "lpq_sphincs_secret_key", header: lpqHeader,
    incompleteStruct.} = object
  LpqAggregate* {.importc: "lpq_aggregate", header: lpqHeader, incompleteStruct.} = object
  LpqVrfKey* {.importc: "lpq_vrf_key", header: lpqHeader, incompleteStruct.} = object

const
  LpqOk* = 0'i32
    ## Success.
  LpqError* = 1'i32
    ## A checked error, or a signature or VRF proof that does not verify; `lpqLastError` has the
    ## message.
  LpqPanic* = 2'i32
    ## The bridge caught a Rust panic.

proc lpqSetup*(threads: csize_t): int32 {.importc: "lpq_setup", header: lpqHeader.}
proc lpqProtocolVersion*(): uint32 {.importc: "lpq_protocol_version", header: lpqHeader.}
proc lpqLastError*(output: ptr LpqBuffer): int32 {.importc: "lpq_last_error", header: lpqHeader.}
proc lpqBufferFree*(data: ptr byte, len: csize_t) {.importc: "lpq_buffer_free", header: lpqHeader.}

proc lpqXmssSecretKeyGenerate*(output: ptr ptr LpqXmssSecretKey): int32 {.
  importc: "lpq_xmss_secret_key_generate", header: lpqHeader.}
proc lpqXmssSecretKeyFromBytes*(
  data: ptr byte, len: csize_t, output: ptr ptr LpqXmssSecretKey): int32 {.
  importc: "lpq_xmss_secret_key_from_bytes", header: lpqHeader.}
proc lpqXmssSecretKeyToBytes*(key: ptr LpqXmssSecretKey, output: ptr LpqBuffer): int32 {.
  importc: "lpq_xmss_secret_key_to_bytes", header: lpqHeader.}
proc lpqXmssSecretKeyCacheToBytes*(key: ptr LpqXmssSecretKey, output: ptr LpqBuffer): int32 {.
  importc: "lpq_xmss_secret_key_cache_to_bytes", header: lpqHeader.}
proc lpqXmssSecretKeyFromCacheBytes*(
  seed: ptr byte, seedLen: csize_t, publicKey: ptr byte, publicKeyLen: csize_t,
  cache: ptr byte, cacheLen: csize_t, output: ptr ptr LpqXmssSecretKey): int32 {.
  importc: "lpq_xmss_secret_key_from_cache_bytes", header: lpqHeader.}
proc lpqXmssSecretKeyPublicKey*(key: ptr LpqXmssSecretKey, output: ptr LpqBuffer): int32 {.
  importc: "lpq_xmss_secret_key_public_key", header: lpqHeader.}
proc lpqXmssSecretKeyPrepare*(key: ptr LpqXmssSecretKey, leafIndex: uint32): int32 {.
  importc: "lpq_xmss_secret_key_prepare", header: lpqHeader.}
proc lpqXmssSecretKeySetBottomTreeCacheSize*(key: ptr LpqXmssSecretKey, size: csize_t): int32 {.
  importc: "lpq_xmss_secret_key_set_bottom_tree_cache_size", header: lpqHeader.}
proc lpqXmssSecretKeySign*(
  key: ptr LpqXmssSecretKey, message: ptr byte, messageLen: csize_t, leafIndex: uint32,
  output: ptr LpqBuffer): int32 {.
  importc: "lpq_xmss_secret_key_sign", header: lpqHeader.}
proc lpqXmssSecretKeyDestroy*(key: ptr LpqXmssSecretKey) {.
  importc: "lpq_xmss_secret_key_destroy", header: lpqHeader.}
proc lpqXmssVerify*(
  publicKey: ptr byte, publicKeyLen: csize_t, message: ptr byte, messageLen: csize_t,
  signature: ptr byte, signatureLen: csize_t): int32 {.
  importc: "lpq_xmss_verify", header: lpqHeader.}

proc lpqSphincsSecretKeyGenerate*(output: ptr ptr LpqSphincsSecretKey): int32 {.
  importc: "lpq_sphincs_secret_key_generate", header: lpqHeader.}
proc lpqSphincsSecretKeyFromSeed*(
  seed: ptr byte, seedLen: csize_t, output: ptr ptr LpqSphincsSecretKey): int32 {.
  importc: "lpq_sphincs_secret_key_from_seed", header: lpqHeader.}
proc lpqSphincsSecretKeyFromBytes*(
  data: ptr byte, len: csize_t, output: ptr ptr LpqSphincsSecretKey): int32 {.
  importc: "lpq_sphincs_secret_key_from_bytes", header: lpqHeader.}
proc lpqSphincsSecretKeyToBytes*(key: ptr LpqSphincsSecretKey, output: ptr LpqBuffer): int32 {.
  importc: "lpq_sphincs_secret_key_to_bytes", header: lpqHeader.}
proc lpqSphincsSecretKeyPublicKey*(key: ptr LpqSphincsSecretKey, output: ptr LpqBuffer): int32 {.
  importc: "lpq_sphincs_secret_key_public_key", header: lpqHeader.}
proc lpqSphincsSecretKeySign*(
  key: ptr LpqSphincsSecretKey, message: ptr byte, messageLen: csize_t,
  output: ptr LpqBuffer): int32 {.
  importc: "lpq_sphincs_secret_key_sign", header: lpqHeader.}
proc lpqSphincsSecretKeyDestroy*(key: ptr LpqSphincsSecretKey) {.
  importc: "lpq_sphincs_secret_key_destroy", header: lpqHeader.}
proc lpqSphincsVerify*(
  publicKey: ptr byte, publicKeyLen: csize_t, message: ptr byte, messageLen: csize_t,
  signature: ptr byte, signatureLen: csize_t): int32 {.
  importc: "lpq_sphincs_verify", header: lpqHeader.}

proc lpqAggregateCreate*(
  children: ptr ptr LpqAggregate, childCount: csize_t,
  xmss: ptr byte, xmssCount: csize_t,
  sphincs: ptr byte, sphincsCount: csize_t,
  output: ptr ptr LpqAggregate): int32 {.
  importc: "lpq_aggregate_create", header: lpqHeader.}
proc lpqAggregateCreateOnly*(
  children: ptr ptr LpqAggregate, childCount: csize_t,
  xmss: ptr byte, xmssCount: csize_t,
  sphincs: ptr byte, sphincsCount: csize_t,
  xmssClaims: ptr byte, xmssClaimCount: csize_t,
  sphincsClaims: ptr byte, sphincsClaimCount: csize_t,
  output: ptr ptr LpqAggregate): int32 {.
  importc: "lpq_aggregate_create_only", header: lpqHeader.}
proc lpqAggregateFromBytes*(
  data: ptr byte, len: csize_t,
  xmssClaims: ptr byte, xmssCount: csize_t,
  sphincsClaims: ptr byte, sphincsCount: csize_t,
  output: ptr ptr LpqAggregate): int32 {.
  importc: "lpq_aggregate_from_bytes", header: lpqHeader.}
proc lpqAggregateToBytes*(aggregate: ptr LpqAggregate, output: ptr LpqBuffer): int32 {.
  importc: "lpq_aggregate_to_bytes", header: lpqHeader.}
proc lpqAggregateXmssClaims*(aggregate: ptr LpqAggregate, output: ptr LpqBuffer): int32 {.
  importc: "lpq_aggregate_xmss_claims", header: lpqHeader.}
proc lpqAggregateSphincsClaims*(aggregate: ptr LpqAggregate, output: ptr LpqBuffer): int32 {.
  importc: "lpq_aggregate_sphincs_claims", header: lpqHeader.}
proc lpqAggregateDestroy*(aggregate: ptr LpqAggregate) {.
  importc: "lpq_aggregate_destroy", header: lpqHeader.}

proc lpqVrfKeyNew*(
  seed: ptr byte, seedLen: csize_t, start, stop: uint32, output: ptr ptr LpqVrfKey): int32 {.
  importc: "lpq_vrf_key_new", header: lpqHeader.}
proc lpqVrfKeyFromCacheBytes*(
  seed: ptr byte, seedLen: csize_t, root: ptr byte, rootLen: csize_t, cache: ptr byte,
  cacheLen: csize_t, output: ptr ptr LpqVrfKey): int32 {.
  importc: "lpq_vrf_key_from_cache_bytes", header: lpqHeader.}
proc lpqVrfKeyCacheToBytes*(key: ptr LpqVrfKey, output: ptr LpqBuffer): int32 {.
  importc: "lpq_vrf_key_cache_to_bytes", header: lpqHeader.}
proc lpqVrfKeyRoot*(key: ptr LpqVrfKey, output: ptr LpqBuffer): int32 {.
  importc: "lpq_vrf_key_root", header: lpqHeader.}
proc lpqVrfKeyProof*(key: ptr LpqVrfKey, slot: uint32, output: ptr LpqBuffer): int32 {.
  importc: "lpq_vrf_key_proof", header: lpqHeader.}
proc lpqVrfKeyDestroy*(key: ptr LpqVrfKey) {.
  importc: "lpq_vrf_key_destroy", header: lpqHeader.}
proc lpqVrfVerify*(
  root: ptr byte, rootLen: csize_t, slot: uint64, proof: ptr byte, proofLen: csize_t): int32 {.
  importc: "lpq_vrf_verify", header: lpqHeader.}
