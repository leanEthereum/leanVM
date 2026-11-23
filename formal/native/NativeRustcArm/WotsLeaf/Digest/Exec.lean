module

public import NativeRustcArm.WotsLeaf.FrameS
public meta import NativeRustcArm.WotsLeaf.FrameS
public meta import NativeRustcArm.Code.Xmss.WotsLeaf

/-!
# The digest's blocks, run by the symbolic executor

`b0` (the prologue, from SP at the entry: the frame's end, `entryS`) and `b1 .. b5` in the frame
(`frameS []`).
-/

namespace NativeRustcArm.WotsLeafProof.Digest

open NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf

@[expose] public section

/-- At the entry: the frame (region 0), SP its end. -/
def entryS : SState := init [(2752, true)] (.ptr 0 2752)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (frameS [])
sym_block run_b2 := exec b2 (frameS [])
sym_block run_b3 := exec b3 (frameS [])
sym_block run_b4 := exec b4 (frameS [])
sym_block run_b5 := exec b5 (frameS [])

end NativeRustcArm.WotsLeafProof.Digest
