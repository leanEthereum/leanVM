module

public import LeanVMCircuits.Rec.Ext
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-!
`E` is a field: `y^3 + y + 1` has no root in `K`. A root `r` has `r^7 = 1`, and `r^(2^64 - 1) = 1` in the field of
`2^64` elements, so `r = r^gcd(7, 2^64 - 1) = 1`, which is not a root. So every nonzero `E` element has an inverse,
and `inv` of one is satisfiable.
-/

namespace LeanVMCircuits.Rec

open Polynomial

/-- `K`'s elements, by their words. -/
noncomputable instance : Fintype K :=
  Fintype.ofInjective (fun x => (⟨toWord x, num_lt _ _⟩ : Fin (2 ^ 64))) fun _ _ h =>
    toWord_injective (Fin.mk.inj_iff.mp h)

theorem card_K : Fintype.card K = 2 ^ 64 := by
  rw [Fintype.card_of_bijective (f := fun x : K => (⟨toWord x, num_lt _ _⟩ : Fin (2 ^ 64)))
    ⟨fun a b h => toWord_injective (Fin.mk.inj_iff.mp h), fun n => ⟨ofWord n, Fin.ext (toWord_ofWord n n.isLt)⟩⟩]
  simp

theorem no_root (r : K) : r ^ 3 + r + 1 ≠ 0 := by
  intro h
  have h7 : r ^ 7 = 1 := by
    linear_combination (r ^ 4 + r ^ 2 + r + 1) * h - (r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1) * two_K
  have hr : r ≠ 0 := by
    rintro rfl
    simp at h
  have hq : r ^ (2 ^ 64 - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one r hr
    rwa [card_K] at this
  have h1 : r ^ Nat.gcd 7 (2 ^ 64 - 1) = 1 := pow_gcd_eq_one.mpr ⟨h7, hq⟩
  rw [show Nat.gcd 7 (2 ^ 64 - 1) = 1 by norm_num, pow_one] at h1
  rw [h1] at h
  exact one_ne_zero (by linear_combination h - two_K)

theorem extModulus_irreducible : Irreducible extModulus := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [extModulus_natDegree]; simp
  · intro x hx
    apply no_root x
    simpa [extModulus, IsRoot] using hx

instance : Fact (Irreducible extModulus) := ⟨extModulus_irreducible⟩

/-- `E` is a field. -/
noncomputable instance : Field E := AdjoinRoot.instField

/-- Every nonzero `E` element has an inverse: an `inv` row of a nonzero element is satisfiable. -/
theorem exists_inverse (a : E) (ha : a ≠ 0) : ∃ i : E, a * i = 1 := ⟨a⁻¹, mul_inv_cancel₀ ha⟩

end LeanVMCircuits.Rec
