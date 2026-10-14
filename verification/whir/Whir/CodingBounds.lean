import Whir.Soundness
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Finite-code list bounds. The list is a deterministic filter of the committed
oracle; no opening strategy or challenge is an argument. -/
namespace Whir.CodingBounds
open scoped BigOperators

noncomputable def agreement {X A : Type*} [Fintype X] (u v : X → A) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => u x = v x).card

noncomputable def candidates {M X A : Type*} [Fintype M] [Fintype X]
    (encode : M → X → A) (oracle : X → A) (threshold : ℕ) : Finset M := by
  classical
  exact Finset.univ.filter fun m => threshold ≤ agreement (encode m) oracle

/-- Johnson's second-moment inequality, derived from the actual agreement
relation. This slightly relaxed integer form avoids square roots and rounding. -/
theorem johnson_second_moment {I X A : Type*} [Fintype I] [Fintype X]
    (code : I → X → A) (oracle : X → A) (t d : ℕ)
    (close : ∀ i, t ≤ agreement (code i) oracle)
    (hd : d ≤ Fintype.card X)
    (pairwise : ∀ i j, i ≠ j → agreement (code i) (code j) ≤ d) :
    (Fintype.card I : ℚ) * ((t : ℚ)^2 - Fintype.card X * d) ≤
      Fintype.card X * (Fintype.card X - (d : ℚ)) := by
  classical
  let a : I → X → ℚ := fun i x => if code i x = oracle x then 1 else 0
  let L : ℚ := Fintype.card I
  let N : ℚ := Fintype.card X
  have row (i : I) : ∑ x, a i x = (agreement (code i) oracle : ℚ) := by
    simp only [a, agreement, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  have low : L * t ≤ ∑ x, ∑ i, a i x := by
    rw [Finset.sum_comm]
    calc
      L * t = ∑ _i : I, (t : ℚ) := by simp [L]
      _ ≤ _ := Finset.sum_le_sum fun i _ => by rw [row]; exact_mod_cast close i
  have overlap (i j : I) : ∑ x, a i x * a j x ≤ if i = j then N else (d : ℚ) := by
    by_cases h : i = j
    · subst j
      simp only [ite_true]
      calc
        _ ≤ ∑ _x : X, (1 : ℚ) := Finset.sum_le_sum fun x _ => by
          dsimp [a]; split_ifs <;> norm_num
        _ = N := by simp [N]
    · rw [ite_eq_right h]
      calc
        _ ≤ (agreement (code i) (code j) : ℚ) := by
          simp only [agreement, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
            Nat.cast_one, Nat.cast_zero]
          apply Finset.sum_le_sum
          intro x _
          dsimp [a]
          split_ifs <;> simp_all
        _ ≤ d := by exact_mod_cast pairwise i j h
  have square : ∑ x, (∑ i, a i x)^2 ≤ L * N + L * (L - 1) * d := by
    simp_rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, ∑ j, ∑ x, a i x * a j x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ ≤ ∑ i : I, ∑ j : I, if i = j then N else (d : ℚ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => overlap i j
      _ = L * N + L * (L - 1) * d := by
        have each (i : I) :
            (∑ j : I, if i = j then N else (d : ℚ)) = N + (L - 1) * d := by
          calc
            _ = ∑ j : I, ((if j = i then N - d else 0) + d) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases h : i = j <;> simp [h, Ne.symm]
            _ = _ := by simp [Finset.sum_add_distrib, L]; ring
        simp_rw [each]
        simp [L]
        ring
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset X)
    (fun _ => (1 : ℚ)) (fun x => ∑ i, a i x)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at cs
  have nonneg : 0 ≤ L * (t : ℚ) := by positivity
  have sqLow : (L * (t : ℚ))^2 ≤ (∑ x, ∑ i, a i x)^2 := by nlinarith
  have upper : (L * (t : ℚ))^2 ≤ N * (L * N + L * (L - 1) * d) :=
    sqLow.trans (cs.trans (mul_le_mul_of_nonneg_left square (by positivity)))
  by_cases hL : L = 0
  · have hd' : (d : ℚ) ≤ N := by dsimp [N]; exact_mod_cast hd
    change L * ((t : ℚ)^2 - N * d) ≤ N * (N - d)
    rw [hL, zero_mul]
    exact mul_nonneg (by dsimp [N]; positivity) (sub_nonneg.mpr hd')
  · have pos : 0 < L := lt_of_le_of_ne (by dsimp [L]; positivity) (Ne.symm hL)
    change L * ((t : ℚ)^2 - N * d) ≤ N * (N - d)
    nlinarith

/-- Exact rational list-size bound above the Johnson agreement threshold. -/
theorem candidates_card {M X A : Type*} [Fintype M] [Fintype X]
    (encode : M → X → A) (oracle : X → A) (t d : ℕ)
    (hd : d ≤ Fintype.card X)
    (pairwise : ∀ i j, i ≠ j → agreement (encode i) (encode j) ≤ d)
    (threshold : (Fintype.card X : ℚ) * d < (t : ℚ)^2) :
    ((candidates encode oracle t).card : ℚ) ≤
      (Fintype.card X * (Fintype.card X - (d : ℚ))) /
        ((t : ℚ)^2 - Fintype.card X * d) := by
  classical
  rw [le_div_iff₀ (sub_pos.mpr threshold)]
  simpa using johnson_second_moment
    (fun i : ↥(candidates encode oracle t) => encode i) oracle t d
    (fun i => (Finset.mem_filter.mp i.property).2) hd
    (fun i j hij => pairwise i j (fun h => hij (Subtype.ext h)))

/-- Annex B's relaxed square-root/slack bound, without an incidence certificate.
The absolute threshold can be the ceiling used in Annex B. -/
theorem annexB_johnson {I X A : Type*} [Fintype I] [Fintype X]
    (code : I → X → A) (oracle : X → A) (t d : ℕ)
    (close : ∀ i, t ≤ agreement (code i) oracle)
    (hd : d ≤ Fintype.card X)
    (pairwise : ∀ i j, i ≠ j → agreement (code i) (code j) ≤ d)
    (rho eta : ℝ) (hrho : 0 < rho) (heta : 0 < eta)
    (hN : 0 < Fintype.card X)
    (rate : (d : ℝ) ≤ rho * Fintype.card X)
    (threshold : (Real.sqrt rho + eta) * Fintype.card X ≤ t) :
    (Fintype.card I : ℝ) ≤ 1 / (2 * eta * Real.sqrt rho) := by
  have h := johnson_second_moment code oracle t d close hd pairwise
  have hreal : (Fintype.card I : ℝ) * ((t : ℝ)^2 - Fintype.card X * d) ≤
      Fintype.card X * (Fintype.card X - (d : ℝ)) := by exact_mod_cast h
  let N : ℝ := Fintype.card X
  let L : ℝ := Fintype.card I
  have npos : 0 < N := by dsimp [N]; exact_mod_cast hN
  have lnonneg : 0 ≤ L := by positivity
  have spos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hs : (Real.sqrt rho)^2 = rho := Real.sq_sqrt hrho.le
  have square : ((Real.sqrt rho + eta) * N)^2 ≤ (t : ℝ)^2 := by
    apply pow_le_pow_left₀ (by positivity) threshold
  have rate' : N * d ≤ rho * N^2 := by
    have := mul_le_mul_of_nonneg_left rate npos.le
    dsimp [N] at *
    nlinarith
  have denom : 2 * eta * Real.sqrt rho * N^2 ≤ (t : ℝ)^2 - N * d := by
    nlinarith [sq_nonneg (eta * N)]
  have combined := mul_le_mul_of_nonneg_left denom lnonneg
  have simple : L * (2 * eta * Real.sqrt rho) * N^2 ≤ 1 * N^2 := by
    have nd : 0 ≤ N * (d : ℝ) := by positivity
    change L * ((t : ℝ)^2 - N * d) ≤ N * (N - d) at hreal
    nlinarith
  have cancelled := (mul_le_mul_iff_left₀ (sq_pos_of_pos npos)).mp simple
  exact (le_div_iff₀ (by positivity)).mpr cancelled

section ReedSolomon
variable {F : Type*} [Field F] [DecidableEq F]

/-- Finite coefficient tables, with all lanes evaluated at the same coordinate. -/
def interleavedEncode {lanes k : ℕ} (v : Fin lanes → Fin k → F)
    (x : F) : Fin lanes → F := fun j => (Polynomial.ofFn k (v j)).eval x

/-- Injectivity of decoding into polynomial coefficient tables, not a
postulated injectivity of the evaluation code. -/
theorem coefficient_tables_injective (lanes k : ℕ) :
    Function.Injective (fun v : Fin lanes → Fin k → F =>
      fun j => Polynomial.ofFn k (v j)) := by
  intro u v h
  funext j
  exact Polynomial.injective_ofFn k (congrFun h j)

theorem interleaved_agreement {lanes k : ℕ} (domain : Finset F)
    (u v : Fin lanes → Fin k → F) (hne : u ≠ v) (hk : 0 < k) :
    (domain.filter fun x => interleavedEncode u x = interleavedEncode v x).card ≤ k - 1 := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hp : Polynomial.ofFn k (u j) ≠ Polynomial.ofFn k (v j) :=
    fun h => hj (Polynomial.injective_ofFn k h)
  calc
    _ ≤ (domain.filter fun x =>
      (Polynomial.ofFn k (u j)).eval x = (Polynomial.ofFn k (v j)).eval x).card :=
      Finset.card_le_card fun x hx => Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).1, congrFun (Finset.mem_filter.mp hx).2 j⟩
    _ ≤ k - 1 := Soundness.evaluation_agreement domain _ _ hp (k - 1)
      (Nat.le_pred_of_lt (Polynomial.ofFn_natDegree_lt hk _))
      (Nat.le_pred_of_lt (Polynomial.ofFn_natDegree_lt hk _))

theorem interleaved_domain_agreement {lanes k : ℕ} (domain : Finset F)
    (u v : Fin lanes → Fin k → F) (hne : u ≠ v) (hk : 0 < k) :
    agreement (fun x : ↥domain => interleavedEncode u x)
      (fun x : ↥domain => interleavedEncode v x) ≤ k - 1 := by
  classical
  have hc : agreement (fun x : ↥domain => interleavedEncode u x)
      (fun x : ↥domain => interleavedEncode v x) =
      (domain.filter fun x => interleavedEncode u x = interleavedEncode v x).card := by
    simp only [agreement, Finset.card_filter]
    exact (Finset.sum_subtype domain (fun _ => Iff.rfl)
      (fun x => if interleavedEncode u x = interleavedEncode v x then 1 else 0)).symm
  rw [hc]
  exact interleaved_agreement domain u v hne hk

/-- Finite interleaved RS candidate list, decoded to coefficient tables and fixed
solely by the committed oracle. Single-lane RS is `lanes = 1`. -/
theorem interleaved_candidates_card [Fintype F] {lanes k : ℕ}
    (domain : Finset F) (oracle : ↥domain → Fin lanes → F) (t : ℕ)
    (hk : 0 < k) (hd : k - 1 ≤ domain.card)
    (threshold : (domain.card : ℚ) * (k - 1 : ℕ) < (t : ℚ)^2) :
    ((candidates (fun v : Fin lanes → Fin k → F =>
      fun x : ↥domain => interleavedEncode v x) oracle t).card : ℚ) ≤
      (domain.card * (domain.card - (k - 1 : ℕ) : ℚ)) /
        ((t : ℚ)^2 - domain.card * (k - 1 : ℕ)) := by
  classical
  simpa using candidates_card
    (fun v : Fin lanes → Fin k → F => fun x : ↥domain => interleavedEncode v x)
    oracle t (k - 1) (by simpa using hd)
    (fun u v hne => interleaved_domain_agreement domain u v hne hk)
    (by simpa using threshold)

end ReedSolomon

end Whir.CodingBounds
