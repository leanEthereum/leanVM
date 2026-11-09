/-
  LeanVM.Guest.B1.Sig.SpWotsCheck

  The facts about numbers `sp_wots`'s soundness reads off its template, checked by the kernel:
  the leaf's cells and the target.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsArms

/-!
# `sp_wots`'s template, checked

* `spLeafCells_eq`: the leaf's cells are `pp`, `a0`, the leaf's `A1` and the 64 tips `spTip i`,
  the slot of chain `i`'s last step in its group;
* `spTarget_eq`: the target's word is `g^128`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- The slot of chain `i`'s last step, in its group. -/
def spTip (i : Nat) : V := .n (spSlot (i / 3 == 0) (spState (i / 3)).2.2 (i % 3) 2)

theorem spLeafCells_eq : spLeafCells = .n 0 :: .n 1 :: .n (spC + 2) :: (List.range 64).map spTip := by
  decide +kernel

/-- `g^128`, the target sum in the exponent. -/
theorem spTarget_eq : spTarget = gen ^ 128 := by
  rw [Value.gen_pow_eq_ofK, spTarget, word, Value.ofBits_zero]
  rw [← ofK_eq_ofLimbs]
  exact congrArg ofK (by decide +kernel)

end
end LeanVM.Guest.B1.Sig
