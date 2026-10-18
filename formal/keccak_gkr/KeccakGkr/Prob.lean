import KeccakGkr.Multilinear
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.ProbabilityBounds
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Schwartz-Zippel at a uniform point

Two distinct polynomials of degree at most `d` agree at a uniform point with probability at
most `d / |E|`, and the multilinear extension of a nonzero table in `n` variables vanishes at a
uniform point with probability at most `n / |E|`.
-/

open Polynomial OracleComp
open scoped ENNReal

namespace KeccakGkr

variable {E : Type} [Field E]

theorem card_eval_eq_le [Fintype E] [DecidableEq E] {p q : E[X]} {d : ℕ} (hpq : p ≠ q) (hp : p.natDegree ≤ d)
    (hq : q.natDegree ≤ d) :
    (Finset.univ.filter fun r => p.eval r = q.eval r).card ≤ d := by
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  calc (Finset.univ.filter fun r => p.eval r = q.eval r).card
      ≤ (p - q).roots.toFinset.card := by
        refine Finset.card_le_card fun r hr => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        simp [Multiset.mem_toFinset, mem_roots hne, hr]
    _ ≤ (p - q).roots.card := Multiset.toFinset_card_le _
    _ ≤ (p - q).natDegree := card_roots' _
    _ ≤ d := (natDegree_sub_le _ _).trans (max_le hp hq)

theorem prob_eval_eq_le [Fintype E] [DecidableEq E] [SampleableType E] {p q : E[X]} {d : ℕ} (hpq : p ≠ q) (hp : p.natDegree ≤ d)
    (hq : q.natDegree ≤ d) :
    Pr{let r ← $ᵗ E}[p.eval r = q.eval r] ≤ d / Fintype.card E := by
  rw [SampleableType.prEvent_uniformSample]
  gcongr
  exact_mod_cast card_eval_eq_le hpq hp hq

theorem mle_snoc {n : ℕ} (g : Cube (n + 1) → E) (r : Fin n → E) (t : E) :
    mle g (Fin.snoc r t) =
      mle (fun x => g (Fin.snoc x false)) r +
        t * (mle (fun x => g (Fin.snoc x true)) r - mle (fun x => g (Fin.snoc x false)) r) := by
  simp only [mle]
  rw [sum_cube_snoc]
  simp only [toPt_snoc, eqPoly_snoc, Fintype.sum_bool, bit_true, bit_false, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => by ring

/-- A nonzero table's multilinear extension vanishes at a uniform point with probability at most
`n / |E|`. -/
theorem prob_mle_eq_zero_le [Fintype E] [DecidableEq E] [SampleableType E] {n : ℕ} (g : Cube n → E) (hg : g ≠ 0) :
    Pr{let r ← $ᵗ (Fin n → E)}[mle g r = 0] ≤ n / Fintype.card E := by
  induction n with
  | zero =>
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun r hr => hg (funext fun x => ?_))
      zero_le
    show g x = 0
    simp only [mle, Finset.univ_unique, eqPoly, Finset.univ_eq_empty, Finset.prod_empty,
      one_mul, Finset.sum_singleton] at hr
    convert hr using 2
  | succ n ih =>
    set g₀ : Cube n → E := fun x => g (Fin.snoc x false)
    set g₁ : Cube n → E := fun x => g (Fin.snoc x true)
    have hg' : g₀ ≠ 0 ∨ g₁ ≠ 0 := by
      by_contra h
      simp only [not_or, not_not] at h
      refine hg (funext fun x => ?_)
      rw [← Fin.snoc_init_self x]
      cases x (Fin.last n)
      · exact congrFun h.1 (Fin.init x)
      · exact congrFun h.2 (Fin.init x)
    have hbad : Pr{let y ← $ᵗ (Fin n → E)}[mle g₀ y = 0 ∧ mle g₁ y = 0] ≤
        n / Fintype.card E := by
      rcases hg' with h | h
      · exact (prEvent_mono _ _ _ fun y hy => hy.1).trans (ih g₀ h)
      · exact (prEvent_mono _ _ _ fun y hy => hy.2).trans (ih g₁ h)
    refine (SampleableType.prEvent_uniformSample_finSnoc_le_add (fun r => mle g r = 0)
      (fun y => mle g₀ y = 0 ∧ mle g₁ y = 0) (ε := 1 / Fintype.card E) fun y hy => ?_).trans ?_
    · have key : ∀ t, mle g (Fin.snoc y t) = mle g₀ y + t * (mle g₁ y - mle g₀ y) :=
        fun t => mle_snoc g y t
      simp only [key]
      by_cases hd : mle g₁ y - mle g₀ y = 0
      · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun t ht => hy ⟨?_, ?_⟩) zero_le
        · simpa [hd] using ht
        · have h0 : mle g₀ y = 0 := by simpa [hd] using ht
          rw [sub_eq_zero] at hd
          rw [hd, h0]
      · have h := prob_eval_eq_le (d := 1) (p := C (mle g₁ y - mle g₀ y) * X + C (mle g₀ y))
          (q := 0) (fun h => hd (by simpa using congrArg (coeff · 1) h)) natDegree_linear_le
          (by simp)
        rw [Nat.cast_one] at h
        refine le_of_eq_of_le (prEvent_congr _ _ _ fun t => ?_) h
        simp only [eval_add, eval_mul, eval_C, eval_X, eval_zero]
        constructor <;> intro h' <;> linear_combination h'
    · rw [Nat.cast_succ, ENNReal.add_div]
      exact add_le_add hbad le_rfl

end KeccakGkr
