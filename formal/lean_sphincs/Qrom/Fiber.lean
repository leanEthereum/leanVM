module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.ENNReal.BigOperators

@[expose] public section

/-!
# Averaging over the data a reveal set leaves hidden

Let `R h` be a set of keys determined by the values of `h` on it: data agreeing with `h` on `R h`
reveal the same set. Then the data split into fibers, the data agreeing on the revealed keys, each a
copy of the values of the other keys, and a sum over the data is the sum over every `h` of the
average over its fiber (`Qrom.sum_eq_sum_fiber`).
-/

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace Qrom

variable {K Z : Type} [Fintype K] [DecidableEq K] [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- `h` on the keys of `R`, and `b` on the others. -/
def merge (R : Finset K) (h : K → Z) (b : {k // k ∉ R} → Z) (k : K) : Z :=
  if hk : k ∈ R then h k else b ⟨k, hk⟩

theorem merge_agree (R : Finset K) (h : K → Z) (b : {k // k ∉ R} → Z) :
    ∀ k ∈ R, merge R h b k = h k := fun k hk ↦ by simp [merge, hk]

variable (R : (K → Z) → Finset K) (hself : ∀ h h', (∀ k ∈ R h, h k = h' k) → R h' = R h)

include hself in
/-- **Averaging over the fibers.** -/
theorem sum_eq_sum_fiber (f : (K → Z) → ℝ≥0∞) :
    ∑ h, f h = ∑ h, (Fintype.card ({k // k ∉ R h} → Z) : ℝ≥0∞)⁻¹ *
      ∑ b : {k // k ∉ R h} → Z, f (merge (R h) h b) := by
  -- the fiber of `h`: the data agreeing with it on `R h`
  set A : (K → Z) → Finset (K → Z) := fun h ↦ Finset.univ.filter fun h' ↦ ∀ k ∈ R h, h' k = h k
  have hmerge : ∀ (f : (K → Z) → ℝ≥0∞) h,
      ∑ b : {k // k ∉ R h} → Z, f (merge (R h) h b) = ∑ h' ∈ A h, f h' := by
    intro f h
    refine Finset.sum_bij (fun b _ ↦ merge (R h) h b) (fun b _ ↦ ?_) (fun b _ b' _ hbb ↦ ?_)
      (fun h' hh' ↦ ?_) fun _ _ ↦ rfl
    · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact merge_agree _ _ _
    · funext k
      have := congrFun hbb k.1
      simpa [merge, k.2] using this
    · refine ⟨fun k ↦ h' k.1, Finset.mem_univ _, ?_⟩
      funext k
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hh'
      by_cases hk : k ∈ R h
      · simp [merge, hk, hh' k hk]
      · simp [merge, hk]
  have hcard : ∀ h, (A h).card = Fintype.card ({k // k ∉ R h} → Z) := by
    intro h
    have := hmerge (fun _ ↦ 1) h
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    exact_mod_cast this.symm
  -- membership in a fiber is symmetric, and fibers reveal the same keys
  have hsymm : ∀ h h', h' ∈ A h ↔ h ∈ A h' := by
    intro h h'
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hh k hk
      rw [hself h h' fun k hk ↦ (hh k hk).symm] at hk
      exact (hh k hk).symm
    · intro hh k hk
      rw [hself h' h fun k hk ↦ (hh k hk).symm] at hk
      exact (hh k hk).symm
  have hR : ∀ h h', h' ∈ A h → R h' = R h := by
    intro h h' hh
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hh
    exact hself h h' fun k hk ↦ (hh k hk).symm
  simp only [hmerge f]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun h' ↦ A h')
    (h := fun h h' ↦ by simp [hsymm])]
  refine Finset.sum_congr rfl fun h' _ ↦ ?_
  rw [Finset.sum_congr rfl fun h hh ↦ by rw [hR h' h hh]]
  rw [Finset.sum_const, nsmul_eq_mul, hcard, ← mul_assoc, ENNReal.mul_inv_cancel
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), one_mul]

end Qrom
