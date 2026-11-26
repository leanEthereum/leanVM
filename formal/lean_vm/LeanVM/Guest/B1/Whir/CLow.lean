/-
  LeanVM.Guest.B1.Whir.CLow

  The inline grinds' range checks read the words `g^i`, `i < 2^11`: memories agreeing there give
  the same honest values.
-/

module

public import LeanVM.Guest.B1.Bits.GrindRc

/-!
# The words the range checks read

`LowAgree rd rd0`: `rd` holds `rd0`'s words at `g^i`, `i < 2^11`. On such memories a range check's
witness (`rcWit_agree`) and so an inline `grind_check`'s honest values (`gcVals_agree`) are the
same, so they can be fixed from `rd0` before the memory.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- `rd` agrees with `rd0` on the words the inline grinds' range checks read, `g^i`, `i < 2^11`. -/
def LowAgree (rd rd0 : Reader) : Prop := ∀ i < 2 ^ 11, rd (addressOfIndex i) = rd0 (addressOfIndex i)

variable {rd rd0 : Reader}

theorem LowAgree.lowDef (h : LowAgree rd rd0) (h0 : LowDef 11 rd0) : LowDef 11 rd := fun i hi ↦ by
  rw [h i hi]; exact h0 i hi

theorem loadHolds_gpow_iff (r : Reader) (j : ℕ) (t : E) :
    LoadHolds r (gen ^ j) 0 t ↔ r (addressOfIndex j) = some t := by
  rw [gen_pow_eq_ofK]
  unfold LoadHolds
  rw [Main.addr_ofK, Nat.add_zero]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨(isInK_iff _).mpr ⟨_, rfl⟩, h⟩⟩

/-- **A range check's witness** at `g^e`, `e < 2^v ≤ 2^11`, is the same on memories agreeing below
`2^11`. -/
theorem rcWit_agree (h : LowAgree rd rd0) {e v : ℕ} (hv : v ≤ 11) (he : e < 2 ^ v) :
    rcWit rd (gen ^ e) (wBound v) = rcWit rd0 (gen ^ e) (wBound v) := by
  have h2 : 2 ^ v ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hv
  have hw : wBound v = gen ^ e * gen ^ (2 ^ v - 1 - e) := by
    rw [wBound_eq hv, ← pow_add, show e + (2 ^ v - 1 - e) = 2 ^ v - 1 by omega]
  have hy : ∀ y : E, wBound v = gen ^ e * y ↔ y = gen ^ (2 ^ v - 1 - e) := by
    intro y
    constructor
    · intro hm; rw [hw] at hm; exact (mul_left_cancel₀ (pow_ne_zero _ gen_ne_zero) hm).symm
    · rintro rfl; exact hw
  have key : ∀ (r : Reader) (p : E × E × E), (LoadHolds r (gen ^ e) 0 p.2.1 ∧ wBound v = gen ^ e * p.1 ∧
      LoadHolds r p.1 0 p.2.2) ↔ (p.1 = gen ^ (2 ^ v - 1 - e) ∧ r (addressOfIndex e) = some p.2.1 ∧
      r (addressOfIndex (2 ^ v - 1 - e)) = some p.2.2) := by
    intro r p
    obtain ⟨y, t1, t2⟩ := p
    simp only [hy, loadHolds_gpow_iff]
    constructor
    · rintro ⟨h1, rfl, h3⟩; exact ⟨rfl, h1, (loadHolds_gpow_iff r _ t2).mp h3⟩
    · rintro ⟨rfl, h1, h3⟩; exact ⟨h1, rfl, (loadHolds_gpow_iff r _ t2).mpr h3⟩
  have hP : (fun p : E × E × E ↦ LoadHolds rd (gen ^ e) 0 p.2.1 ∧ wBound v = gen ^ e * p.1 ∧
      LoadHolds rd p.1 0 p.2.2) = (fun p : E × E × E ↦ LoadHolds rd0 (gen ^ e) 0 p.2.1 ∧
      wBound v = gen ^ e * p.1 ∧ LoadHolds rd0 p.1 0 p.2.2) := by
    funext p
    apply propext
    rw [key rd p, key rd0 p, h e (by omega), h _ (by omega)]
  unfold rcWit
  rw [hP]

theorem gcIterVal_agree (h : LowAgree rd rd0) (b : ℕ) (w tabs : E) (i r : ℕ) :
    gcIterVal rd b w tabs i r = gcIterVal rd0 b w tabs i r := by
  have e := rcWit_agree h (le_refl 11) (Nat.mod_lt (gcV b w i) (by norm_num : 0 < 2 ^ 11))
  rcases r with _ | _ | _ | _ | r <;> simp only [gcIterVal, e]

/-- **An inline grind's honest values** are the same on memories agreeing below `2^11`. -/
theorem gcVals_agree (h : LowAgree rd rd0) {b : ℕ} (hb : b ∈ grindBitsDeployed) (w tabs : E) (k : ℕ) :
    gcVals rd b w tabs k = gcVals rd0 b w tabs k := by
  obtain ⟨-, hT, hsum⟩ := gc_shape b hb
  have e := rcWit_agree h hT (gcV_zero_lt hsum w)
  unfold gcVals
  simp only [e, gcIterVal_agree h]

end
end LeanVM.Guest.B1
