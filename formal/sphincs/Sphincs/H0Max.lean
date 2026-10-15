import Sphincs.H0Psi2

/-! **The codeword-level sums are expectations over the componentwise maximum.** With `u`
independent uniform codewords and `M` their componentwise maximum, `f(u) = E[H(M)]` and
`f2(u) = E[H(M)^2]`, `H(m)` the probability that a uniform codeword is at most `m`: the signed
sums over chosen chains are inclusion-exclusion of "every needed chain is reached by some
codeword". -/

open ENNReal

namespace Sphincs.Security.H0

open Concrete

set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-- The componentwise maximum of codewords, on the grid `{0..4}^6`. -/
def maxCw {u : ℕ} (c : Fin u → LutIdx) (i : FChain) : FPos :=
  ⟨Finset.univ.sup fun k => (lut (c k) i).val, by
    apply Nat.lt_succ_of_le
    exact Finset.sup_le fun k _ => Nat.le_of_lt_succ (lut (c k) i).isLt⟩

/-- The probability that a uniform codeword is at most `m`. -/
noncomputable def Hm (m : FChain → FPos) : ℝ :=
  avgR fun w : LutIdx => if ∀ i, (lut w i).val ≤ (m i).val then 1 else 0

theorem avgR_comm {α β : Type} [Fintype α] [Fintype β] (h : α → β → ℝ) :
    avgR (fun a => avgR fun b => h a b) = avgR fun b => avgR fun a => h a b := by
  unfold avgR
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem avgR_pow_prod {u : ℕ} (g : LutIdx → ℝ) :
    avgR (fun c : Fin u → LutIdx => ∏ k, g (c k)) = avgR g ^ u := by
  rw [avgR_prod_pi (fun _ => g), Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem le_maxCw_iff {u : ℕ} (c : Fin u → LutIdx) (i : FChain) (x : ℕ) :
    x ≤ (maxCw c i).val ↔ x = 0 ∨ ∃ k, x ≤ (lut (c k) i).val := by
  unfold maxCw
  simp only
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      have hpos : ⊥ < x := Nat.pos_of_ne_zero hx
      by_contra hno
      push Not at hno
      have hlt : (Finset.univ.sup fun k => (lut (c k) i).val) < x :=
        (Finset.sup_lt_iff hpos).2 fun k _ => hno k
      omega
  · rintro (h | ⟨k, hk⟩)
    · rw [h]; exact Nat.zero_le _
    · exact le_trans hk (Finset.le_sup (f := fun k => (lut (c k) i).val) (Finset.mem_univ k))

/-- The inclusion-exclusion of reaching every needed chain. -/
theorem signed_reach (w : LutIdx) {u : ℕ} (c : Fin u → LutIdx) :
    ∑ T : Finset FChain, (-1) ^ T.card * needA1 w T *
      ∏ k, ∏ i ∈ T, (if (lut (c k) i).val < (lut w i).val then (1 : ℝ) else 0) =
      if ∀ i, (lut w i).val ≤ (maxCw c i).val then 1 else 0 := by
  classical
  have hpt : ∀ i, (1 - (if (lut w i).val = 0 then (0 : ℝ) else 1) *
      ∏ k, (if (lut (c k) i).val < (lut w i).val then (1 : ℝ) else 0)) =
      if (lut w i).val ≤ (maxCw c i).val then 1 else 0 := by
    intro i
    by_cases h0 : (lut w i).val = 0
    · rw [if_pos h0, zero_mul, sub_zero, if_pos (by rw [h0]; exact Nat.zero_le _)]
    · rw [if_neg h0, one_mul]
      by_cases hr : ∃ k, (lut w i).val ≤ (lut (c k) i).val
      · obtain ⟨k, hk⟩ := hr
        rw [Finset.prod_eq_zero (Finset.mem_univ k) (if_neg (by omega)), sub_zero,
          if_pos ((le_maxCw_iff c i _).2 (Or.inr ⟨k, hk⟩))]
      · push Not at hr
        rw [Finset.prod_eq_one fun k _ => if_pos (hr k), sub_self, if_neg]
        intro hle
        rcases (le_maxCw_iff c i _).1 hle with h | ⟨k, hk⟩
        · exact h0 h
        · exact absurd (hr k) (by omega)
  have hprod : (if ∀ i, (lut w i).val ≤ (maxCw c i).val then (1 : ℝ) else 0) =
      ∏ i, (1 - (if (lut w i).val = 0 then (0 : ℝ) else 1) *
        ∏ k, (if (lut (c k) i).val < (lut w i).val then (1 : ℝ) else 0)) := by
    simp only [hpt]
    by_cases hall : ∀ i, (lut w i).val ≤ (maxCw c i).val
    · rw [if_pos hall]
      exact (Finset.prod_eq_one fun i _ => if_pos (hall i)).symm
    · rw [if_neg hall]
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (by omega))).symm
  rw [hprod, prod_one_sub_mul]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold needA1
  rw [Finset.prod_comm]

/-- **`f(u) = E[H(M)]`.** -/
theorem fR_eq_max (u : ℕ) : fR u = avgR fun c : Fin u → LutIdx => Hm (maxCw c) := by
  unfold fR G Hm
  have hpow : ∀ (w : LutIdx) (T : Finset FChain), (avgR fun w' : LutIdx =>
      ∏ i ∈ T, (if (lut w' i).val < (lut w i).val then (1 : ℝ) else 0)) ^ u =
      avgR fun c : Fin u → LutIdx => ∏ k, ∏ i ∈ T, (if (lut (c k) i).val < (lut w i).val then (1 : ℝ) else 0) :=
    fun w T => (avgR_pow_prod (fun w' => ∏ i ∈ T, if (lut w' i).val < (lut w i).val then (1 : ℝ) else 0)).symm
  simp only [hpow]
  have hin : ∀ w : LutIdx, (∑ T : Finset FChain, (-1) ^ T.card * needA1 w T *
      avgR fun c : Fin u → LutIdx => ∏ k, ∏ i ∈ T, (if (lut (c k) i).val < (lut w i).val then (1 : ℝ) else 0)) =
      avgR fun c : Fin u → LutIdx => if ∀ i, (lut w i).val ≤ (maxCw c i).val then 1 else 0 := by
    intro w
    simp only [← avgR_const_mul, ← avgR_sum]
    exact congrArg avgR (funext fun c => signed_reach w c)
  simp only [hin]
  exact avgR_comm _

/-- **`f2(u) = E[H(M)^2]`.** -/
theorem f2R_eq_max (u : ℕ) : f2R u = avgR fun c : Fin u → LutIdx => Hm (maxCw c) ^ 2 := by
  unfold f2R G2
  have hpow : ∀ (w : LutIdx) (T : Finset FChain) (w' : LutIdx) (T' : Finset FChain), (avgR fun v : LutIdx =>
      (∏ i ∈ T, (if (lut v i).val < (lut w i).val then (1 : ℝ) else 0)) *
        ∏ i ∈ T', (if (lut v i).val < (lut w' i).val then (1 : ℝ) else 0)) ^ u =
      avgR fun c : Fin u → LutIdx => (∏ k, ∏ i ∈ T, (if (lut (c k) i).val < (lut w i).val then (1 : ℝ) else 0)) *
        ∏ k, ∏ i ∈ T', (if (lut (c k) i).val < (lut w' i).val then (1 : ℝ) else 0) := by
    intro w T w' T'
    rw [← avgR_pow_prod]
    simp only [Finset.prod_mul_distrib]
  simp only [hpow]
  have hin : ∀ ww : LutIdx × LutIdx, (∑ T : Finset FChain, ∑ T' : Finset FChain,
      ((-1) ^ T.card * needA1 ww.1 T) * ((-1) ^ T'.card * needA1 ww.2 T') *
        avgR fun c : Fin u → LutIdx => (∏ k, ∏ i ∈ T, (if (lut (c k) i).val < (lut ww.1 i).val then (1 : ℝ) else 0)) *
          ∏ k, ∏ i ∈ T', (if (lut (c k) i).val < (lut ww.2 i).val then (1 : ℝ) else 0)) =
      avgR fun c : Fin u → LutIdx => (if ∀ i, (lut ww.1 i).val ≤ (maxCw c i).val then (1 : ℝ) else 0) *
        if ∀ i, (lut ww.2 i).val ≤ (maxCw c i).val then 1 else 0 := by
    intro ww
    simp only [← avgR_const_mul, ← avgR_sum]
    refine congrArg avgR (funext fun c => ?_)
    rw [← signed_reach ww.1 c, ← signed_reach ww.2 c, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun T' _ => ?_
    ring
  simp only [hin]
  have hsw : (avgR fun ww : LutIdx × LutIdx => avgR fun c : Fin u → LutIdx =>
      (if ∀ i, (lut ww.1 i).val ≤ (maxCw c i).val then (1 : ℝ) else 0) *
        if ∀ i, (lut ww.2 i).val ≤ (maxCw c i).val then 1 else 0) =
      avgR fun c : Fin u → LutIdx => avgR fun ww : LutIdx × LutIdx =>
        (if ∀ i, (lut ww.1 i).val ≤ (maxCw c i).val then (1 : ℝ) else 0) *
          if ∀ i, (lut ww.2 i).val ≤ (maxCw c i).val then 1 else 0 := by
    exact avgR_comm _
  rw [hsw]
  refine congrArg avgR (funext fun c => ?_)
  rw [avgR_prod_split (fun w : LutIdx => if ∀ i, (lut w i).val ≤ (maxCw c i).val then (1 : ℝ) else 0)
    (fun w : LutIdx => if ∀ i, (lut w i).val ≤ (maxCw c i).val then (1 : ℝ) else 0), sq]
  rfl

end Sphincs.Security.H0
