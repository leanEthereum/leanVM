module

public import NativeRustcX64.WotsLeaf.Epilogue
public meta import NativeRustcX64.WotsLeaf.Epilogue
public meta import NativeRustcX64.Code.Xmss.WotsLeaf

/-!
# The leaf's blocks, run by the symbolic executor

`b51` (the leaf's address at `112`, `memset` of the leaf's hasher at `2352`), `b52 .. b54` (its
`update`s, RBX the hasher), `b55` (`finalize` into `1048`), `b56` (the digits and the leaf's first
16 bytes copied to `112 .. 186`, `memcpy` to `out + 1`), `b57` (the tag 1 at `out`, `out` as
region 4, RBX its base).
-/

namespace NativeRustcX64.WotsLeafProof.Leaf

open NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf

set_option Elab.async false

sym_block run_b51 := exec b51 (frameS [])
sym_block run_b52 := exec b52 (frameS [(.rbx, .ptr 0 2352)])
sym_block run_b53 := exec b53 (frameS [(.rbx, .ptr 0 2352)])
sym_block run_b54 := exec b54 (frameS [(.rbx, .ptr 0 2352)])
sym_block run_b55 := exec b55 (frameS [(.rbx, .ptr 0 2352)])
sym_block run_b56 := exec b56 (frameS [])
sym_block run_b57 := exec b57 (outS [(.rbx, .ptr 4 0)])

end NativeRustcX64.WotsLeafProof.Leaf
