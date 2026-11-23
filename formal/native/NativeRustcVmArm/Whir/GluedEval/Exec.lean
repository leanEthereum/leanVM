module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.GluedEval
public meta import NativeRustcVmArm.Code.Vm.GluedEval
public import NativeRustcVmArm.Whir.MathFrame
public meta import NativeRustcVmArm.Whir.Common

/-!
# `glued_eval`'s blocks, run by the symbolic executor

`entryS`: region 0 the 16 bytes below SP (the frame of the `eq` branch), region 1 the glued claim
(X1, 6064 bytes). `b0` tests the kind; `b1` (kind `≠ 0`) sets up `induced_weight`'s arguments and
jumps there; `b2` (kind `0`) pushes X30, X19 and calls `eq_eval`; `b3` (`retS`: region 0 the frame
from SP, region 1 the `Option<EW>` X19 points to) stores `Some` and returns.
-/

namespace NativeRustcVmArm.Whir.GluedEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GluedEval

@[expose] public section

/-- At the entry: the frame below SP (region 0), the glued claim (region 1, X1). -/
def entryS : SState := init [(16, true), (6064, false)] (.ptr 0 16) [(.X1, .ptr 1 0)]

/-- After `eq_eval`: the frame from SP (region 0), the output X19 points to (region 1). -/
def retS : SState := init [(16, true), (24, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- The slots `b2` saves. -/
def slots : List (Nat × XReg) := [(0, .X30), (8, .X19)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 (after b0 entryS)
sym_block run_b3 := exec b3 retS

public theorem b2_frame : (∀ p ∈ slots, p.1 + 8 ≤ 16 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b2 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b2 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    (∀ r ∈ freeRegs slots, (after b2 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b2_mem : ∀ w ∈ (after b2 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 16 := by
  decide +kernel

public theorem b1_keeps : keeps entryS (after b1 (after b0 entryS)) = true := by decide +kernel

public theorem b3_restores : restores slots 16 (after b3 retS) = true := by decide +kernel

public theorem b3_mem : ∀ w ∈ (after b3 retS).mem, w.r = 1 ∧ w.off + w.n ≤ 24 := by
  decide +kernel

end NativeRustcVmArm.Whir.GluedEval
