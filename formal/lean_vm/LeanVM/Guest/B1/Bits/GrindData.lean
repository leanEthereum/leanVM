/-
  LeanVM.Guest.B1.Bits.GrindData

  The shape facts of `grind_check`'s expansion (`GrindT`).
-/

module

public import LeanVM.Guest.B1.Bits.MeaningP
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.B1.Bits.GrindT

/-!
# `grind_check`'s expansion: its shape facts

The template `gcPre b` and its inlining `gcInlineT` are in `GrindT`, which reads no core data, so a
template module can state an inlined grind without importing the guest's bodies.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The windows tile the lane above `b`: the top window is `1 ..= 11` bits and ends at bit `63`. -/
theorem gc_shape : ∀ b ∈ grindBitsDeployed,
    1 ≤ gcTop b ∧ gcTop b ≤ 11 ∧ b + 11 * gcW b + gcTop b = 64 := by
  decide

theorem gcW_pos : ∀ b ∈ grindBitsDeployed, 1 ≤ gcW b := by decide

/-- Every value of the expansion is one of its `gcLen b`. -/
theorem gcPre_vals : ∀ b ∈ grindBitsDeployed,
    (Stmt.valsList (gcPre b)).all (fun v => decide (v = .n v.idx ∧ v.idx < gcLen b)) = true := by
  decide

end
end LeanVM.Guest.B1
