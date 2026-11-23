module

public import NativeRustcX64.WotsLeaf.FrameS
public meta import NativeRustcX64.WotsLeaf.FrameS
public meta import NativeRustcX64.Code.Xmss.WotsLeaf

/-!
# The digest's blocks, run by the symbolic executor

`b0` (the prologue, from RSP at the entry: the frame's byte `2760`, `entryS`) and `b1 .. b5` in
the frame (`frameS []`).
-/

namespace NativeRustcX64.WotsLeafProof.Digest

open NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf

@[expose] public section

/-- At the entry: the frame (region 0) and the call's return slot (region 1), RSP the return
address's place. -/
def entryS : SState :=
  ((init [2784, 8, 8, 8] [(.rsp, .ptr 0 2760)] [] []
    [(.ptr 0 (-8), (1, 0)), (.gotSlot "memcpy", 2, 0), (.gotSlot "memset", 3, 0)]).withKnownBytes
    2 0 8 (.label "memcpy")).withKnownBytes 3 0 8 (.label "memset")

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (frameS [])
sym_block run_b2 := exec b2 (frameS [])
sym_block run_b3 := exec b3 (frameS [])
sym_block run_b4 := exec b4 (frameS [])
sym_block run_b5 := exec b5 (frameS [])

end NativeRustcX64.WotsLeafProof.Digest
