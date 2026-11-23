/-
  LeanVM.Guest.B1.Bits.GrindRc

  The inlined grind's range checks pass on every memory defined below `2^11`, apart from its
  placement (`GrindPlaced`), so that a template's proof can use it without importing the guest's
  bodies.
-/

module

public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.Memory.LowDef

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- **The windows' range checks pass** on every memory defined below `2^κ`, `11 ≤ κ`. -/
theorem gcRc_of_lowDef {κ : ℕ} (hκ : 11 ≤ κ) {rd : Reader} (hlow : LowDef κ rd) :
    ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2 := by
  intro v hv e he
  obtain ⟨a, b, c⟩ := rc_complete_low hlow (K := 2 ^ v)
    (Nat.pow_le_pow_right (by decide) (by omega)) he
  refine ⟨_, _, _, by rw [gen_pow_eq_ofK]; exact a, ?_, c⟩
  rw [wBound_eq hv, gen_pow_eq_ofK, gen_pow_eq_ofK]
  exact b

end
end LeanVM.Guest.B1
