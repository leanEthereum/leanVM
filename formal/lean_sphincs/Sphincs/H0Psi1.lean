import Sphincs.H0Moments

/-! **The first per-tree moment.** The one-mark avoidance probability decodes into the
codeword-level probability `G(w, T)` that a uniform codeword stays below codeword `w` on the chains
`T`: `Q = 15/16 + 1/16 Π_j (7/8 + G_j / 8)`. Binomial expansions turn the signed sum of `Q^n` into
`Ψ1(n) = Σ_i C(n,i) (15/16)^(n-i) (1/16)^i μ_i^2`, `μ_i = Σ_u C(i,u) (7/8)^(i-u) (1/8)^u f(u)`, with
`f(u)` the signed codeword-level sum. -/

open ENNReal

namespace Sphincs.Security.H0

open Concrete

set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-! ### The one-mark avoidance probability -/

/-- A uniform codeword stays strictly below codeword `w` on the chains `T`. -/
noncomputable def G (w : LutIdx) (T : Finset FChain) : ℝ :=
  avgR fun w' : LutIdx => ∏ i ∈ T, if (lut w' i).val < (lut w i).val then 1 else 0

theorem avgR_ite_one {β : Type} [Fintype β] [DecidableEq β] (b0 : β) (V : ℝ) :
    avgR (fun b : β => if b = b0 then V else 1) =
      ((Fintype.card β : ℝ) - 1) / Fintype.card β + V / Fintype.card β := by
  unfold avgR
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_eq' Finset.univ b0, ite_eq_left (Finset.mem_univ _),
    Finset.card_singleton, nsmul_eq_mul, nsmul_eq_mul, Finset.filter_ne' Finset.univ b0,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hc : (1 : ℕ) ≤ Fintype.card β := Fintype.card_pos_iff.2 ⟨b0⟩
  rw [Nat.cast_sub hc]
  have hc0 : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hc)
  field_simp
  ring

/-- The avoidance probability given the mark's tree leaf. -/
theorem avgR_avoidB_inner (t : MT) (S : SubIdx → Finset FChain) (s : SuperIdx) :
    (avgR fun p : SubIdx → ChildIdx × LutIdx => avoidB t S (s, p)) =
      if s = t.1 then ∏ j, (7 / 8 + 1 / 8 * G (t.2 j).2 (S j)) else 1 := by
  classical
  by_cases hst : s = t.1
  · rw [ite_eq_left hst]
    subst hst
    have hprod : ∀ p : SubIdx → ChildIdx × LutIdx, avoidB t S (t.1, p) =
        ∏ j, ∏ i ∈ S j, (1 - if (p j).1 = (t.2 j).1 ∧ need t j i ≤ (lut (p j).2 i).val then (1 : ℝ) else 0) := by
      intro p
      unfold avoidB KC need
      refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i _ => ?_
      simp
    simp only [hprod]
    rw [avgR_prod_pi (fun j (q : ChildIdx × LutIdx) =>
      ∏ i ∈ S j, (1 - if q.1 = (t.2 j).1 ∧ need t j i ≤ (lut q.2 i).val then (1 : ℝ) else 0))]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [avgR_prod_type]
    have ha : ∀ a : ChildIdx, (avgR fun w : LutIdx => ∏ i ∈ S j,
        (1 - if (a, w).1 = (t.2 j).1 ∧ need t j i ≤ (lut (a, w).2 i).val then (1 : ℝ) else 0)) =
        if a = (t.2 j).1 then G (t.2 j).2 (S j) else 1 := by
      intro a
      by_cases ha : a = (t.2 j).1
      · rw [ite_eq_left ha]
        unfold G
        congr 1
        funext w
        refine Finset.prod_congr rfl fun i _ => ?_
        simp only [ha, true_and, need]
        by_cases hlt : (lut w i).val < (lut (t.2 j).2 i).val
        · rw [ite_eq_right (by omega), ite_eq_left hlt]; ring
        · rw [ite_eq_left (by omega), ite_eq_right hlt]; ring
      · rw [ite_eq_right ha]
        have h1 : ∀ w : LutIdx, (∏ i ∈ S j,
            (1 - if (a, w).1 = (t.2 j).1 ∧ need t j i ≤ (lut (a, w).2 i).val then (1 : ℝ) else 0)) = 1 :=
          fun w => Finset.prod_eq_one fun i _ => by rw [ite_eq_right (fun h => ha h.1), sub_zero]
        simp only [h1]
        exact avgR_const 1
    simp only [ha]
    rw [avgR_ite_one]
    simp only [ChildIdx, Fintype.card_fin]
    norm_num [subHeight]
    ring
  · rw [ite_eq_right hst]
    have hone : ∀ p : SubIdx → ChildIdx × LutIdx, avoidB t S (s, p) = 1 := by
      intro p
      unfold avoidB
      refine Finset.prod_eq_one fun j _ => Finset.prod_eq_one fun i _ => ?_
      rw [ite_eq_right (fun h => hst h.1), sub_zero]
    simp only [hone]
    exact avgR_const 1

/-- **Decoding the avoidance probability.** -/
theorem avgR_avoidB (t : MT) (S : SubIdx → Finset FChain) :
    avgR (avoidB t S) = 15 / 16 + 1 / 16 * ∏ j, (7 / 8 + 1 / 8 * G (t.2 j).2 (S j)) := by
  classical
  rw [avgR_prod_type]
  have hs := avgR_avoidB_inner t S
  simp only [hs]
  rw [avgR_ite_one]
  simp only [SuperIdx, Fintype.card_fin]
  norm_num [topHeight]
  ring

/-! ### The first moment -/

/-- The first per-tree moment: the probability that a uniform target is covered by `n` uniform
marks. -/
noncomputable def Ψ1R (n : ℕ) : ℝ := avgNR (fun X : Multiset MT => avgR fun t : MT => coverR t X) n 0

/-- The chosen chains of one subtree are needed by codeword `w`. -/
noncomputable def needA1 (w : LutIdx) (T : Finset FChain) : ℝ := ∏ i ∈ T, if (lut w i).val = 0 then 0 else 1

/-- The signed codeword-level sum `f(u)`. -/
noncomputable def fR (u : ℕ) : ℝ :=
  avgR fun w : LutIdx => ∑ T : Finset FChain, (-1) ^ T.card * needA1 w T * G w T ^ u

/-- The per-subtree factor `μ_i`. -/
noncomputable def μR (i : ℕ) : ℝ :=
  avgR fun w : LutIdx => ∑ T : Finset FChain, (-1) ^ T.card * needA1 w T * (1 / 8 * G w T + 7 / 8) ^ i

theorem avgNR_avgR {β α : Type} [Fintype β] [Fintype α] (φ : β → Multiset α → ℝ) (n : ℕ) (X0 : Multiset α) :
    avgNR (fun X => avgR fun b => φ b X) n X0 = avgR fun b => avgNR (φ b) n X0 := by
  unfold avgR
  rw [avgNR_const_mul, avgNR_sum]

theorem avgR_words (F : (SubIdx → LutIdx) → ℝ) :
    avgR (fun t : MT => F fun j => (t.2 j).2) = avgR F := by
  rw [avgR_prod_type]
  have h1 : (fun b : SuperIdx => avgR fun c : SubIdx → ChildIdx × LutIdx => F fun j => ((b, c).2 j).2) =
      fun _ => avgR (fun c : SubIdx → ChildIdx × LutIdx => F fun j => (c j).2) := rfl
  rw [h1, avgR_const]
  have he : ∀ g : (SubIdx → ChildIdx × LutIdx) → ℝ, avgR g =
      avgR (fun q : (SubIdx → ChildIdx) × (SubIdx → LutIdx) => g ((Equiv.arrowProdEquivProdArrow _ _ _).symm q)) :=
    fun g => avgR_equiv (Equiv.arrowProdEquivProdArrow SubIdx (fun _ => ChildIdx) (fun _ => LutIdx)) g
  rw [he, avgR_prod_type]
  have h2 : (fun b : SubIdx → ChildIdx => avgR fun c : SubIdx → LutIdx =>
      F fun j => (((Equiv.arrowProdEquivProdArrow SubIdx (fun _ => ChildIdx) (fun _ => LutIdx)).symm (b, c)) j).2) =
      fun _ => avgR F := rfl
  rw [h2, avgR_const]

theorem Ψ1R_signed (n : ℕ) :
    Ψ1R n = avgR fun t : MT => ∑ S : SubIdx → Finset FChain, sgnS S * needA t S * avgR (avoidB t S) ^ n := by
  unfold Ψ1R
  rw [avgNR_avgR]
  refine congrArg avgR (funext fun t => ?_)
  have hc : (fun X : Multiset MT => coverR t X) = fun X => ∑ S : SubIdx → Finset FChain,
      sgnS S * needA t S * (X.map (avoidB t S)).prod := funext fun X => coverR_expand t X
  rw [show (coverR t) = fun X : Multiset MT => coverR t X from rfl, hc, avgNR_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [avgNR_const_mul, avgNR_prod_map, Multiset.map_zero, Multiset.prod_zero, one_mul]

theorem needA_eq (t : MT) (S : SubIdx → Finset FChain) : needA t S = ∏ j, needA1 (t.2 j).2 (S j) := rfl

/-- Binomial expansion of an affine power. -/
theorem pow_affine (c d P : ℝ) (n : ℕ) :
    (c + d * P) ^ n = ∑ i ∈ Finset.range (n + 1), d ^ i * c ^ (n - i) * (n.choose i : ℝ) * P ^ i := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow]
  ring

/-- **The first moment.** -/
theorem Ψ1R_eq (n : ℕ) :
    Ψ1R n = ∑ i ∈ Finset.range (n + 1), (1 / 16) ^ i * (15 / 16) ^ (n - i) * (n.choose i : ℝ) * μR i ^ 2 := by
  rw [Ψ1R_signed]
  simp only [avgR_avoidB, needA_eq]
  rw [avgR_words (fun w => ∑ S : SubIdx → Finset FChain, sgnS S * (∏ j, needA1 (w j) (S j)) *
    (15 / 16 + 1 / 16 * ∏ j, (7 / 8 + 1 / 8 * G (w j) (S j))) ^ n)]
  have hexp : ∀ w : SubIdx → LutIdx, (∑ S : SubIdx → Finset FChain, sgnS S * (∏ j, needA1 (w j) (S j)) *
      (15 / 16 + 1 / 16 * ∏ j, (7 / 8 + 1 / 8 * G (w j) (S j))) ^ n) =
      ∑ i ∈ Finset.range (n + 1), (1 / 16) ^ i * (15 / 16) ^ (n - i) * (n.choose i : ℝ) *
        ∏ j, ∑ T : Finset FChain, (-1) ^ T.card * needA1 (w j) T * (1 / 8 * G (w j) T + 7 / 8) ^ i := by
    intro w
    simp only [pow_affine (15 / 16 : ℝ) (1 / 16 : ℝ), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.prod_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    unfold sgnS
    rw [← Finset.prod_pow]
    have h78 : ∀ j, (7 / 8 + 1 / 8 * G (w j) (S j) : ℝ) = 1 / 8 * G (w j) (S j) + 7 / 8 := fun j => by ring
    simp only [h78, Finset.prod_mul_distrib]
    ring
  simp only [hexp]
  rw [avgR_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [avgR_const_mul, avgR_prod_pi (fun _ w => ∑ T : Finset FChain, (-1) ^ T.card * needA1 w T *
    (1 / 8 * G w T + 7 / 8) ^ i)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- **The per-subtree factor.** -/
theorem μR_eq (i : ℕ) :
    μR i = ∑ u ∈ Finset.range (i + 1), (1 / 8) ^ u * (7 / 8) ^ (i - u) * (i.choose u : ℝ) * fR u := by
  unfold μR fR
  have hpt : ∀ w : LutIdx, (∑ T : Finset FChain, (-1) ^ T.card * needA1 w T * (1 / 8 * G w T + 7 / 8) ^ i) =
      ∑ u ∈ Finset.range (i + 1), (1 / 8) ^ u * (7 / 8) ^ (i - u) * (i.choose u : ℝ) *
        ∑ T : Finset FChain, (-1) ^ T.card * needA1 w T * G w T ^ u := by
    intro w
    have hT : ∀ T : Finset FChain, (1 / 8 * G w T + 7 / 8) ^ i =
        ∑ u ∈ Finset.range (i + 1), (1 / 8) ^ u * (7 / 8) ^ (i - u) * (i.choose u : ℝ) * G w T ^ u := by
      intro T
      rw [add_comm]
      exact pow_affine _ _ _ _
    simp only [hT, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun T _ => ?_
    ring
  simp only [hpt]
  rw [avgR_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [avgR_const_mul]

end Sphincs.Security.H0
