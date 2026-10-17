import Sphincs.H0Psi1

/-! **The second per-tree moment.** Two targets covered by the same marks: the one-mark avoidance
probability of both targets' chosen chains decodes by cases on whether the targets share their
tree leaf and, per subtree, their WOTS key; with a shared key the two codewords' constraints merge
into `G2`. -/

open ENNReal

namespace Sphincs.Security.H0

open Concrete

set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-- A uniform codeword stays below `w` on `T` and below `w'` on `T'`. -/
noncomputable def G2 (w : LutIdx) (T : Finset FChain) (w' : LutIdx) (T' : Finset FChain) : ℝ :=
  avgR fun v : LutIdx => (∏ i ∈ T, if (lut v i).val < (lut w i).val then 1 else 0) *
    ∏ i ∈ T', if (lut v i).val < (lut w' i).val then 1 else 0

/-- The per-subtree avoidance factor of two targets with the same tree leaf. -/
noncomputable def βf (e : Bool) (w : LutIdx) (T : Finset FChain) (w' : LutIdx) (T' : Finset FChain) : ℝ :=
  if e then 7 / 8 + 1 / 8 * G2 w T w' T' else 6 / 8 + 1 / 8 * G w T + 1 / 8 * G w' T'

theorem avgR_ite_two {β : Type} [Fintype β] [DecidableEq β] (b0 b1 : β) (h : b0 ≠ b1) (V0 V1 : ℝ) :
    avgR (fun b : β => if b = b0 then V0 else if b = b1 then V1 else 1) =
      ((Fintype.card β : ℝ) - 2) / Fintype.card β + V0 / Fintype.card β + V1 / Fintype.card β := by
  haveI : Nonempty β := ⟨b0⟩
  have hsplit : (fun b : β => if b = b0 then V0 else if b = b1 then V1 else 1) =
      fun b => (if b = b0 then V0 - 1 else 0) + ((if b = b1 then V1 - 1 else 0) + 1) := by
    funext b
    by_cases h0 : b = b0
    · subst h0; simp [h]
    · by_cases h1 : b = b1
      · subst h1; simp [h0]
      · simp [h0, h1]
  rw [hsplit, avgR_add, avgR_add, avgR_const]
  unfold avgR
  rw [Finset.sum_ite_eq' Finset.univ b0, Finset.sum_ite_eq' Finset.univ b1, if_pos (Finset.mem_univ _),
    if_pos (Finset.mem_univ _)]
  have hc0 : (Fintype.card β : ℝ) ≠ 0 := by
    have : 0 < Fintype.card β := Fintype.card_pos_iff.2 ⟨b0⟩
    exact_mod_cast this.ne'
  field_simp
  ring

/-- The per-subtree average of the joint avoidance of two targets with the same tree leaf. -/
theorem avg_pair_sub (j : SubIdx) (t t' : MT) (T T' : Finset FChain) :
    (avgR fun q : ChildIdx × LutIdx =>
      (∏ i ∈ T, (1 - if q.1 = (t.2 j).1 ∧ need t j i ≤ (lut q.2 i).val then (1 : ℝ) else 0)) *
        ∏ i ∈ T', (1 - if q.1 = (t'.2 j).1 ∧ need t' j i ≤ (lut q.2 i).val then (1 : ℝ) else 0)) =
      βf (decide ((t.2 j).1 = (t'.2 j).1)) (t.2 j).2 T (t'.2 j).2 T' := by
  classical
  rw [avgR_prod_type]
  have hlt : ∀ (tt : MT) (w : LutIdx) (i : FChain), (1 - if need tt j i ≤ (lut w i).val then (1 : ℝ) else 0) =
      if (lut w i).val < (lut (tt.2 j).2 i).val then 1 else 0 := by
    intro tt w i
    unfold need
    by_cases h : (lut w i).val < (lut (tt.2 j).2 i).val
    · rw [if_neg (by omega), if_pos h]; ring
    · rw [if_pos (by omega), if_neg h]; ring
  have hcard : (Fintype.card ChildIdx : ℝ) = 8 := by
    show (Fintype.card (Fin (2 ^ subHeight)) : ℝ) = 8
    rw [Fintype.card_fin]
    norm_num [subHeight]
  by_cases he : (t.2 j).1 = (t'.2 j).1
  · rw [show decide ((t.2 j).1 = (t'.2 j).1) = true from decide_eq_true he]
    have ha : ∀ a : ChildIdx, (avgR fun w : LutIdx =>
        (∏ i ∈ T, (1 - if (a, w).1 = (t.2 j).1 ∧ need t j i ≤ (lut (a, w).2 i).val then (1 : ℝ) else 0)) *
          ∏ i ∈ T', (1 - if (a, w).1 = (t'.2 j).1 ∧ need t' j i ≤ (lut (a, w).2 i).val then (1 : ℝ) else 0)) =
        if a = (t.2 j).1 then G2 (t.2 j).2 T (t'.2 j).2 T' else 1 := by
      intro a
      by_cases ha : a = (t.2 j).1
      · rw [if_pos ha]
        unfold G2
        congr 1
        funext w
        simp only [ha, he, true_and]
        congr 1
        · exact Finset.prod_congr rfl fun i _ => hlt t w i
        · exact Finset.prod_congr rfl fun i _ => hlt t' w i
      · rw [if_neg ha]
        have ha' : a ≠ (t'.2 j).1 := fun h => ha (h.trans he.symm)
        have h1 : ∀ w : LutIdx, (∏ i ∈ T, (1 - if (a, w).1 = (t.2 j).1 ∧ need t j i ≤ (lut (a, w).2 i).val then
            (1 : ℝ) else 0)) * ∏ i ∈ T', (1 - if (a, w).1 = (t'.2 j).1 ∧ need t' j i ≤ (lut (a, w).2 i).val then
            (1 : ℝ) else 0) = 1 := by
          intro w
          rw [Finset.prod_eq_one fun i _ => by rw [if_neg (fun h => ha h.1), sub_zero],
            Finset.prod_eq_one fun i _ => by rw [if_neg (fun h => ha' h.1), sub_zero], one_mul]
        simp only [h1]
        exact avgR_const 1
    simp only [ha]
    rw [avgR_ite_one, hcard, βf, if_pos rfl]
    ring
  · rw [show decide ((t.2 j).1 = (t'.2 j).1) = false from decide_eq_false he]
    have ha : ∀ a : ChildIdx, (avgR fun w : LutIdx =>
        (∏ i ∈ T, (1 - if (a, w).1 = (t.2 j).1 ∧ need t j i ≤ (lut (a, w).2 i).val then (1 : ℝ) else 0)) *
          ∏ i ∈ T', (1 - if (a, w).1 = (t'.2 j).1 ∧ need t' j i ≤ (lut (a, w).2 i).val then (1 : ℝ) else 0)) =
        if a = (t.2 j).1 then G (t.2 j).2 T else if a = (t'.2 j).1 then G (t'.2 j).2 T' else 1 := by
      intro a
      by_cases ha : a = (t.2 j).1
      · rw [if_pos ha]
        have ha' : a ≠ (t'.2 j).1 := fun h => he (ha.symm.trans h)
        unfold G
        congr 1
        funext w
        rw [Finset.prod_eq_one (s := T') fun i _ => by rw [if_neg (fun h => ha' h.1), sub_zero], mul_one]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp only [ha, true_and]
        exact hlt t w i
      · rw [if_neg ha]
        by_cases ha' : a = (t'.2 j).1
        · rw [if_pos ha']
          unfold G
          congr 1
          funext w
          rw [Finset.prod_eq_one (s := T) fun i _ => by rw [if_neg (fun h => ha h.1), sub_zero], one_mul]
          refine Finset.prod_congr rfl fun i _ => ?_
          simp only [ha', true_and]
          exact hlt t' w i
        · rw [if_neg ha']
          have h1 : ∀ w : LutIdx, (∏ i ∈ T, (1 - if (a, w).1 = (t.2 j).1 ∧ need t j i ≤ (lut (a, w).2 i).val then
              (1 : ℝ) else 0)) * ∏ i ∈ T', (1 - if (a, w).1 = (t'.2 j).1 ∧ need t' j i ≤ (lut (a, w).2 i).val then
              (1 : ℝ) else 0) = 1 := by
            intro w
            rw [Finset.prod_eq_one fun i _ => by rw [if_neg (fun h => ha h.1), sub_zero],
              Finset.prod_eq_one fun i _ => by rw [if_neg (fun h => ha' h.1), sub_zero], one_mul]
          simp only [h1]
          exact avgR_const 1
    simp only [ha]
    rw [avgR_ite_two _ _ he, hcard, βf, if_neg (by simp)]
    ring


theorem avoidB_off (t : MT) (S : SubIdx → Finset FChain) (s : SuperIdx) (p : SubIdx → ChildIdx × LutIdx)
    (h : s ≠ t.1) : avoidB t S (s, p) = 1 := by
  unfold avoidB
  exact Finset.prod_eq_one fun j _ => Finset.prod_eq_one fun i _ => by rw [if_neg (fun h' => h h'.1), sub_zero]

theorem avoidB_on (t : MT) (S : SubIdx → Finset FChain) (p : SubIdx → ChildIdx × LutIdx) :
    avoidB t S (t.1, p) =
      ∏ j, ∏ i ∈ S j, (1 - if (p j).1 = (t.2 j).1 ∧ need t j i ≤ (lut (p j).2 i).val then (1 : ℝ) else 0) := by
  unfold avoidB KC need
  refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i _ => ?_
  simp

/-- **Decoding the joint avoidance probability of two targets.** -/
theorem avgR_avoid2 (t t' : MT) (S S' : SubIdx → Finset FChain) :
    avgR (fun x => avoidB t S x * avoidB t' S' x) =
      if t.1 = t'.1 then
        15 / 16 + 1 / 16 * ∏ j, βf (decide ((t.2 j).1 = (t'.2 j).1)) (t.2 j).2 (S j) (t'.2 j).2 (S' j)
      else 14 / 16 + 1 / 16 * ∏ j, (7 / 8 + 1 / 8 * G (t.2 j).2 (S j)) +
        1 / 16 * ∏ j, (7 / 8 + 1 / 8 * G (t'.2 j).2 (S' j)) := by
  classical
  rw [avgR_prod_type]
  have hcard : (Fintype.card SuperIdx : ℝ) = 16 := by
    show (Fintype.card (Fin (2 ^ topHeight)) : ℝ) = 16
    rw [Fintype.card_fin]
    norm_num [topHeight]
  by_cases hst : t.1 = t'.1
  · rw [if_pos hst]
    have hs : ∀ s : SuperIdx, (avgR fun p : SubIdx → ChildIdx × LutIdx => avoidB t S (s, p) * avoidB t' S' (s, p)) =
        if s = t.1 then ∏ j, βf (decide ((t.2 j).1 = (t'.2 j).1)) (t.2 j).2 (S j) (t'.2 j).2 (S' j) else 1 := by
      intro s
      by_cases hs : s = t.1
      · rw [if_pos hs]
        subst hs
        have hprod : ∀ p : SubIdx → ChildIdx × LutIdx, avoidB t S (t.1, p) * avoidB t' S' (t.1, p) =
            ∏ j, ((∏ i ∈ S j, (1 - if (p j).1 = (t.2 j).1 ∧ need t j i ≤ (lut (p j).2 i).val then (1 : ℝ) else 0)) *
              ∏ i ∈ S' j, (1 - if (p j).1 = (t'.2 j).1 ∧ need t' j i ≤ (lut (p j).2 i).val then (1 : ℝ) else 0)) := by
          intro p
          rw [avoidB_on, hst, avoidB_on, ← Finset.prod_mul_distrib]
        simp only [hprod]
        rw [avgR_prod_pi (fun j (q : ChildIdx × LutIdx) =>
          (∏ i ∈ S j, (1 - if q.1 = (t.2 j).1 ∧ need t j i ≤ (lut q.2 i).val then (1 : ℝ) else 0)) *
            ∏ i ∈ S' j, (1 - if q.1 = (t'.2 j).1 ∧ need t' j i ≤ (lut q.2 i).val then (1 : ℝ) else 0))]
        exact Finset.prod_congr rfl fun j _ => avg_pair_sub j t t' (S j) (S' j)
      · rw [if_neg hs]
        have h1 : ∀ p : SubIdx → ChildIdx × LutIdx, avoidB t S (s, p) * avoidB t' S' (s, p) = 1 := fun p => by
          rw [avoidB_off t S s p hs, avoidB_off t' S' s p (fun h => hs (h.trans hst.symm)), one_mul]
        simp only [h1]
        exact avgR_const 1
    simp only [hs]
    rw [avgR_ite_one, hcard]
    ring
  · rw [if_neg hst]
    have hs : ∀ s : SuperIdx, (avgR fun p : SubIdx → ChildIdx × LutIdx => avoidB t S (s, p) * avoidB t' S' (s, p)) =
        if s = t.1 then ∏ j, (7 / 8 + 1 / 8 * G (t.2 j).2 (S j))
        else if s = t'.1 then ∏ j, (7 / 8 + 1 / 8 * G (t'.2 j).2 (S' j)) else 1 := by
      intro s
      by_cases hs : s = t.1
      · rw [if_pos hs]
        have h1 : ∀ p : SubIdx → ChildIdx × LutIdx, avoidB t S (s, p) * avoidB t' S' (s, p) = avoidB t S (s, p) :=
          fun p => by rw [avoidB_off t' S' s p (fun h => hst (hs.symm.trans h)), mul_one]
        simp only [h1]
        rw [avgR_avoidB_inner, if_pos hs]
      · rw [if_neg hs]
        by_cases hs' : s = t'.1
        · rw [if_pos hs']
          have h1 : ∀ p : SubIdx → ChildIdx × LutIdx, avoidB t S (s, p) * avoidB t' S' (s, p) =
              avoidB t' S' (s, p) := fun p => by rw [avoidB_off t S s p hs, one_mul]
          simp only [h1]
          rw [avgR_avoidB_inner, if_pos hs']
        · rw [if_neg hs']
          have h1 : ∀ p : SubIdx → ChildIdx × LutIdx, avoidB t S (s, p) * avoidB t' S' (s, p) = 1 := fun p => by
            rw [avoidB_off t S s p hs, avoidB_off t' S' s p hs', one_mul]
          simp only [h1]
          exact avgR_const 1
    simp only [hs]
    rw [avgR_ite_two _ _ hst, hcard]
    ring

/-! ### The second moment -/

/-- The second per-tree moment: the probability that two independent uniform targets are both
covered by `n` uniform marks. -/
noncomputable def Ψ2R (n : ℕ) : ℝ := avgNR (fun X : Multiset MT => (avgR fun t : MT => coverR t X) ^ 2) n 0

theorem avgR_sq {α : Type} [Fintype α] (g : α → ℝ) :
    avgR g ^ 2 = avgR fun tt : α × α => g tt.1 * g tt.2 := by
  rw [avgR_prod_type, sq]
  have h : ∀ a : α, (avgR fun b : α => g (a, b).1 * g (a, b).2) = g a * avgR g := fun a => avgR_const_mul (g a) g
  simp only [h]
  rw [show (fun a => g a * avgR g) = fun a => avgR g * g a from funext fun a => mul_comm _ _, avgR_const_mul]

theorem coverR_mul_expand (t t' : MT) (X : Multiset MT) :
    coverR t X * coverR t' X = ∑ S : SubIdx → Finset FChain, ∑ S' : SubIdx → Finset FChain,
      (sgnS S * needA t S) * (sgnS S' * needA t' S') * (X.map fun x => avoidB t S x * avoidB t' S' x).prod := by
  rw [coverR_expand, coverR_expand, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun S' _ => ?_
  rw [Multiset.prod_map_mul]
  ring

theorem Ψ2R_signed (n : ℕ) :
    Ψ2R n = avgR fun tt : MT × MT => ∑ S : SubIdx → Finset FChain, ∑ S' : SubIdx → Finset FChain,
      (sgnS S * needA tt.1 S) * (sgnS S' * needA tt.2 S') *
        avgR (fun x => avoidB tt.1 S x * avoidB tt.2 S' x) ^ n := by
  unfold Ψ2R
  simp only [avgR_sq]
  rw [avgNR_avgR]
  refine congrArg avgR (funext fun tt => ?_)
  have hc : (fun X : Multiset MT => coverR tt.1 X * coverR tt.2 X) = fun X => ∑ S : SubIdx → Finset FChain,
      ∑ S' : SubIdx → Finset FChain, (sgnS S * needA tt.1 S) * (sgnS S' * needA tt.2 S') *
        (X.map fun x => avoidB tt.1 S x * avoidB tt.2 S' x).prod := funext fun X => coverR_mul_expand _ _ X
  rw [hc, avgNR_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [avgNR_sum]
  refine Finset.sum_congr rfl fun S' _ => ?_
  rw [avgNR_const_mul, avgNR_prod_map, Multiset.map_zero, Multiset.prod_zero, one_mul]

/-! ### Generic sums and averages over pairs -/

theorem sum_pair_prod {κ A : Type} [Fintype κ] [DecidableEq κ] [Fintype A] (h : κ → A → A → ℝ) :
    ∑ S : κ → A, ∑ S' : κ → A, ∏ j, h j (S j) (S' j) = ∏ j, ∑ a : A, ∑ a' : A, h j a a' := by
  rw [← Fintype.sum_prod_type' (f := fun S S' : κ → A => ∏ j, h j (S j) (S' j)),
    ← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow κ (fun _ => A) (fun _ => A))]
  simp only [Equiv.arrowProdEquivProdArrow_apply]
  rw [← Fintype.prod_sum (fun j (x : A × A) => h j x.1 x.2)]
  simp only [Fintype.sum_prod_type']

theorem avgR_pair_pi {κ C : Type} [Fintype κ] [DecidableEq κ] [Fintype C] (K : κ → C → C → ℝ) :
    avgR (fun pp : (κ → C) × (κ → C) => ∏ j, K j (pp.1 j) (pp.2 j)) =
      ∏ j, avgR fun cc : C × C => K j cc.1 cc.2 := by
  rw [avgR_equiv (Equiv.arrowProdEquivProdArrow κ (fun _ => C) (fun _ => C)).symm]
  simp only [Equiv.symm_symm, Equiv.arrowProdEquivProdArrow_apply]
  exact avgR_prod_pi (fun j (cc : C × C) => K j cc.1 cc.2)

theorem avgR_pair_ite {β : Type} [Fintype β] [DecidableEq β] [Nonempty β] (A B : ℝ) :
    avgR (fun bb : β × β => if bb.1 = bb.2 then A else B) =
      A / Fintype.card β + B * ((Fintype.card β : ℝ) - 1) / Fintype.card β := by
  rw [avgR_prod_type]
  have h : ∀ b : β, (avgR fun b' : β => if (b, b').1 = (b, b').2 then A else B) =
      ((Fintype.card β : ℝ) - 1) / Fintype.card β * B + A / Fintype.card β := by
    intro b
    have := avgR_ite_one (β := β) b (A / B)
    by_cases hB : B = 0
    · simp only [hB]
      have h2 : (fun b' : β => if (b, b').1 = (b, b').2 then A else (0 : ℝ)) = fun b' => if b' = b then A else 0 := by
        funext b'
        simp only [eq_comm]
      rw [h2]
      unfold avgR
      rw [Finset.sum_ite_eq' Finset.univ b, if_pos (Finset.mem_univ _)]
      ring
    · have h2 : (fun b' : β => if (b, b').1 = (b, b').2 then A else B) =
          fun b' => B * (if b' = b then A / B else 1) := by
        funext b'
        by_cases hb : b' = b
        · rw [if_pos hb, if_pos hb.symm]; field_simp
        · rw [if_neg hb, if_neg (Ne.symm hb), mul_one]
      rw [h2, avgR_const_mul, this]
      field_simp
  simp only [h]
  rw [avgR_const]
  ring

/-- The average over a pair of tuples factors through the components. -/
theorem avgR_pair_prod_type {β γ : Type} [Fintype β] [Fintype γ] (g : (β × γ) × (β × γ) → ℝ) :
    avgR g = avgR fun bb : β × β => avgR fun cc : γ × γ => g ((bb.1, cc.1), (bb.2, cc.2)) := by
  rw [avgR_equiv (Equiv.prodProdProdComm β γ β γ)]
  rw [avgR_prod_type]
  rfl

/-! ### The second moment in closed form -/

/-- The signed codeword-level sum `f2(u)` of two targets sharing a WOTS key. -/
noncomputable def f2R (u : ℕ) : ℝ :=
  avgR fun ww : LutIdx × LutIdx => ∑ T : Finset FChain, ∑ T' : Finset FChain,
    ((-1) ^ T.card * needA1 ww.1 T) * ((-1) ^ T'.card * needA1 ww.2 T') * G2 ww.1 T ww.2 T' ^ u

/-- The per-subtree factor of two targets sharing a WOTS key. -/
noncomputable def νeqR (i : ℕ) : ℝ :=
  avgR fun ww : LutIdx × LutIdx => ∑ T : Finset FChain, ∑ T' : Finset FChain,
    ((-1) ^ T.card * needA1 ww.1 T) * ((-1) ^ T'.card * needA1 ww.2 T') * βf true ww.1 T ww.2 T' ^ i

/-- The per-subtree factor of two targets with different WOTS keys. -/
noncomputable def νneR (i : ℕ) : ℝ :=
  avgR fun ww : LutIdx × LutIdx => ∑ T : Finset FChain, ∑ T' : Finset FChain,
    ((-1) ^ T.card * needA1 ww.1 T) * ((-1) ^ T'.card * needA1 ww.2 T') * βf false ww.1 T ww.2 T' ^ i

/-- The per-subtree factor of two targets with the same tree leaf. -/
noncomputable def νR (i : ℕ) : ℝ := 1 / 8 * νeqR i + 7 / 8 * νneR i

theorem avgR_words' (F : (SubIdx → LutIdx) → ℝ) :
    avgR (fun p : SubIdx → ChildIdx × LutIdx => F fun j => (p j).2) = avgR F := by
  rw [avgR_equiv (Equiv.arrowProdEquivProdArrow SubIdx (fun _ => ChildIdx) (fun _ => LutIdx)), avgR_prod_type]
  have h2 : (fun b : SubIdx → ChildIdx => avgR fun c : SubIdx → LutIdx =>
      F fun j => (((Equiv.arrowProdEquivProdArrow SubIdx (fun _ => ChildIdx) (fun _ => LutIdx)).symm (b, c)) j).2) =
      fun _ => avgR F := rfl
  rw [h2, avgR_const]

/-- The average of a signed product over a uniform pair of codewords is the square of `μ`. -/
theorem avg_signed_pow (i : ℕ) :
    avgR (fun w : SubIdx → LutIdx => ∑ S : SubIdx → Finset FChain, sgnS S * (∏ j, needA1 (w j) (S j)) *
      (∏ j, (7 / 8 + 1 / 8 * G (w j) (S j))) ^ i) = μR i ^ 2 := by
  have hpt : ∀ w : SubIdx → LutIdx, (∑ S : SubIdx → Finset FChain, sgnS S * (∏ j, needA1 (w j) (S j)) *
      (∏ j, (7 / 8 + 1 / 8 * G (w j) (S j))) ^ i) =
      ∏ j, ∑ T : Finset FChain, (-1) ^ T.card * needA1 (w j) T * (1 / 8 * G (w j) T + 7 / 8) ^ i := by
    intro w
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    unfold sgnS
    rw [← Finset.prod_pow]
    have h78 : ∀ j, (7 / 8 + 1 / 8 * G (w j) (S j) : ℝ) = 1 / 8 * G (w j) (S j) + 7 / 8 := fun j => by ring
    simp only [h78, Finset.prod_mul_distrib]
  simp only [hpt]
  rw [avgR_prod_pi (fun _ w => ∑ T : Finset FChain, (-1) ^ T.card * needA1 w T * (1 / 8 * G w T + 7 / 8) ^ i),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- Binomial expansion of a power of an affine form in two variables. -/
theorem pow_affine2 (c d x y : ℝ) (n : ℕ) :
    (c + d * x + d * y) ^ n = ∑ s ∈ Finset.range (n + 1), d ^ s * c ^ (n - s) * (n.choose s : ℝ) *
      ∑ i ∈ Finset.range (s + 1), (s.choose i : ℝ) * x ^ i * y ^ (s - i) := by
  rw [show c + d * x + d * y = c + d * (x + y) by ring, pow_affine]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [add_pow, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Expansion of a double signed sum of powers of an affine form. -/
theorem sum_sum_pow_affine2 {A B : Type} [Fintype A] [Fintype B] (a : A → ℝ) (b : B → ℝ) (x : A → ℝ) (y : B → ℝ)
    (c d : ℝ) (n : ℕ) :
    ∑ S : A, ∑ S' : B, a S * b S' * (c + d * x S + d * y S') ^ n =
      ∑ s ∈ Finset.range (n + 1), d ^ s * c ^ (n - s) * (n.choose s : ℝ) *
        ∑ i ∈ Finset.range (s + 1), (s.choose i : ℝ) * (∑ S : A, a S * x S ^ i) * ∑ S' : B, b S' * y S' ^ (s - i) := by
  have hterm : ∀ S S', a S * b S' * (c + d * x S + d * y S') ^ n =
      ∑ s ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (s + 1),
        d ^ s * c ^ (n - s) * (n.choose s : ℝ) * ((s.choose i : ℝ) * (a S * x S ^ i) * (b S' * y S' ^ (s - i))) := by
    intro S S'
    rw [pow_affine2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [hterm]
  have h1 : ∀ S : A, (∑ S' : B, ∑ s ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (s + 1),
      d ^ s * c ^ (n - s) * (n.choose s : ℝ) * ((s.choose i : ℝ) * (a S * x S ^ i) * (b S' * y S' ^ (s - i)))) =
      ∑ s ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (s + 1), ∑ S' : B,
        d ^ s * c ^ (n - s) * (n.choose s : ℝ) * ((s.choose i : ℝ) * (a S * x S ^ i) * (b S' * y S' ^ (s - i))) := by
    intro S
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_comm
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem avgR_prod_split {β : Type} [Fintype β] (F G : β → ℝ) :
    avgR (fun pp : β × β => F pp.1 * G pp.2) = avgR F * avgR G := by
  rw [avgR_prod_type]
  have h : ∀ b : β, (avgR fun b' : β => F (b, b').1 * G (b, b').2) = F b * avgR G := fun b => avgR_const_mul (F b) G
  simp only [h]
  rw [show (fun b => F b * avgR G) = fun b => avgR G * F b from funext fun b => mul_comm _ _, avgR_const_mul,
    mul_comm]

/-- The part of two targets with different tree leaves. -/
theorem avg_ne_part (n : ℕ) :
    avgR (fun pp : (SubIdx → ChildIdx × LutIdx) × (SubIdx → ChildIdx × LutIdx) =>
      ∑ S : SubIdx → Finset FChain, ∑ S' : SubIdx → Finset FChain,
        (sgnS S * ∏ j, needA1 (pp.1 j).2 (S j)) * (sgnS S' * ∏ j, needA1 (pp.2 j).2 (S' j)) *
          (14 / 16 + 1 / 16 * (∏ j, (7 / 8 + 1 / 8 * G (pp.1 j).2 (S j))) +
            1 / 16 * ∏ j, (7 / 8 + 1 / 8 * G (pp.2 j).2 (S' j))) ^ n) =
      ∑ s ∈ Finset.range (n + 1), (1 / 16) ^ s * (14 / 16) ^ (n - s) * (n.choose s : ℝ) *
        ∑ i ∈ Finset.range (s + 1), (s.choose i : ℝ) * μR i ^ 2 * μR (s - i) ^ 2 := by
  simp only [sum_sum_pow_affine2]
  rw [avgR_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [avgR_const_mul, avgR_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsplit := avgR_prod_split (fun p : SubIdx → ChildIdx × LutIdx => ∑ S : SubIdx → Finset FChain,
      sgnS S * (∏ j, needA1 (p j).2 (S j)) * (∏ j, (7 / 8 + 1 / 8 * G (p j).2 (S j))) ^ i)
    (fun p : SubIdx → ChildIdx × LutIdx => ∑ S : SubIdx → Finset FChain,
      sgnS S * (∏ j, needA1 (p j).2 (S j)) * (∏ j, (7 / 8 + 1 / 8 * G (p j).2 (S j))) ^ (s - i))
  rw [show (fun pp : (SubIdx → ChildIdx × LutIdx) × (SubIdx → ChildIdx × LutIdx) => (s.choose i : ℝ) *
      (∑ S : SubIdx → Finset FChain, sgnS S * (∏ j, needA1 (pp.1 j).2 (S j)) *
        (∏ j, (7 / 8 + 1 / 8 * G (pp.1 j).2 (S j))) ^ i) *
      ∑ S' : SubIdx → Finset FChain, sgnS S' * (∏ j, needA1 (pp.2 j).2 (S' j)) *
        (∏ j, (7 / 8 + 1 / 8 * G (pp.2 j).2 (S' j))) ^ (s - i)) =
      fun pp => (s.choose i : ℝ) * ((∑ S : SubIdx → Finset FChain, sgnS S * (∏ j, needA1 (pp.1 j).2 (S j)) *
        (∏ j, (7 / 8 + 1 / 8 * G (pp.1 j).2 (S j))) ^ i) *
      ∑ S' : SubIdx → Finset FChain, sgnS S' * (∏ j, needA1 (pp.2 j).2 (S' j)) *
        (∏ j, (7 / 8 + 1 / 8 * G (pp.2 j).2 (S' j))) ^ (s - i)) from funext fun pp => by ring]
  rw [avgR_const_mul, hsplit,
    avgR_words' (fun w => ∑ S : SubIdx → Finset FChain, sgnS S * (∏ j, needA1 (w j) (S j)) *
      (∏ j, (7 / 8 + 1 / 8 * G (w j) (S j))) ^ i),
    avgR_words' (fun w => ∑ S : SubIdx → Finset FChain, sgnS S * (∏ j, needA1 (w j) (S j)) *
      (∏ j, (7 / 8 + 1 / 8 * G (w j) (S j))) ^ (s - i)),
    avg_signed_pow, avg_signed_pow]
  ring


/-- The per-subtree factor averaged over a pair of (WOTS key, codeword) choices. -/
theorem avg_child_pair (i : ℕ) :
    avgR (fun cc : (ChildIdx × LutIdx) × (ChildIdx × LutIdx) => ∑ T : Finset FChain, ∑ T' : Finset FChain,
      ((-1) ^ T.card * needA1 cc.1.2 T) * ((-1) ^ T'.card * needA1 cc.2.2 T') *
        βf (decide (cc.1.1 = cc.2.1)) cc.1.2 T cc.2.2 T' ^ i) = νR i := by
  rw [avgR_pair_prod_type]
  have h : ∀ aa : ChildIdx × ChildIdx, (avgR fun ww : LutIdx × LutIdx => ∑ T : Finset FChain, ∑ T' : Finset FChain,
      ((-1) ^ T.card * needA1 ((aa.1, ww.1), (aa.2, ww.2)).1.2 T) *
        ((-1) ^ T'.card * needA1 ((aa.1, ww.1), (aa.2, ww.2)).2.2 T') *
        βf (decide (((aa.1, ww.1), (aa.2, ww.2)).1.1 = ((aa.1, ww.1), (aa.2, ww.2)).2.1))
          ((aa.1, ww.1), (aa.2, ww.2)).1.2 T ((aa.1, ww.1), (aa.2, ww.2)).2.2 T' ^ i) =
      if aa.1 = aa.2 then νeqR i else νneR i := by
    intro aa
    by_cases ha : aa.1 = aa.2
    · rw [if_pos ha]
      unfold νeqR
      congr 1
      funext ww
      simp only [ha, decide_true]
    · rw [if_neg ha]
      unfold νneR
      congr 1
      funext ww
      simp only [ha, decide_false]
  simp only [h]
  rw [avgR_pair_ite]
  have hcard : (Fintype.card ChildIdx : ℝ) = 8 := by
    show (Fintype.card (Fin (2 ^ subHeight)) : ℝ) = 8
    rw [Fintype.card_fin]
    norm_num [subHeight]
  rw [hcard, νR]
  ring

/-- The part of two targets with the same tree leaf. -/
theorem avg_eq_part (n : ℕ) :
    avgR (fun pp : (SubIdx → ChildIdx × LutIdx) × (SubIdx → ChildIdx × LutIdx) =>
      ∑ S : SubIdx → Finset FChain, ∑ S' : SubIdx → Finset FChain,
        (sgnS S * ∏ j, needA1 (pp.1 j).2 (S j)) * (sgnS S' * ∏ j, needA1 (pp.2 j).2 (S' j)) *
          (15 / 16 + 1 / 16 * ∏ j, βf (decide ((pp.1 j).1 = (pp.2 j).1)) (pp.1 j).2 (S j) (pp.2 j).2 (S' j)) ^ n) =
      ∑ i ∈ Finset.range (n + 1), (1 / 16) ^ i * (15 / 16) ^ (n - i) * (n.choose i : ℝ) * νR i ^ 2 := by
  have hpt : ∀ pp : (SubIdx → ChildIdx × LutIdx) × (SubIdx → ChildIdx × LutIdx),
      (∑ S : SubIdx → Finset FChain, ∑ S' : SubIdx → Finset FChain,
        (sgnS S * ∏ j, needA1 (pp.1 j).2 (S j)) * (sgnS S' * ∏ j, needA1 (pp.2 j).2 (S' j)) *
          (15 / 16 + 1 / 16 * ∏ j, βf (decide ((pp.1 j).1 = (pp.2 j).1)) (pp.1 j).2 (S j) (pp.2 j).2 (S' j)) ^ n) =
      ∑ i ∈ Finset.range (n + 1), (1 / 16) ^ i * (15 / 16) ^ (n - i) * (n.choose i : ℝ) *
        ∏ j, ∑ T : Finset FChain, ∑ T' : Finset FChain,
          ((-1) ^ T.card * needA1 (pp.1 j).2 T) * ((-1) ^ T'.card * needA1 (pp.2 j).2 T') *
            βf (decide ((pp.1 j).1 = (pp.2 j).1)) (pp.1 j).2 T (pp.2 j).2 T' ^ i := by
    intro pp
    simp only [pow_affine, Finset.mul_sum]
    have hsw : ∀ S : SubIdx → Finset FChain, (∑ S' : SubIdx → Finset FChain, ∑ i ∈ Finset.range (n + 1),
        (sgnS S * ∏ j, needA1 (pp.1 j).2 (S j)) * (sgnS S' * ∏ j, needA1 (pp.2 j).2 (S' j)) *
          ((1 / 16) ^ i * (15 / 16) ^ (n - i) * (n.choose i : ℝ) *
            (∏ j, βf (decide ((pp.1 j).1 = (pp.2 j).1)) (pp.1 j).2 (S j) (pp.2 j).2 (S' j)) ^ i)) =
        ∑ i ∈ Finset.range (n + 1), ∑ S' : SubIdx → Finset FChain,
          (sgnS S * ∏ j, needA1 (pp.1 j).2 (S j)) * (sgnS S' * ∏ j, needA1 (pp.2 j).2 (S' j)) *
            ((1 / 16) ^ i * (15 / 16) ^ (n - i) * (n.choose i : ℝ) *
              (∏ j, βf (decide ((pp.1 j).1 = (pp.2 j).1)) (pp.1 j).2 (S j) (pp.2 j).2 (S' j)) ^ i) :=
      fun S => Finset.sum_comm
    simp only [hsw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_pair_prod (fun j T T' => ((-1) ^ T.card * needA1 (pp.1 j).2 T) * ((-1) ^ T'.card * needA1 (pp.2 j).2 T') *
      βf (decide ((pp.1 j).1 = (pp.2 j).1)) (pp.1 j).2 T (pp.2 j).2 T' ^ i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S' _ => ?_
    unfold sgnS
    rw [← Finset.prod_pow]
    simp only [Finset.prod_mul_distrib]
    ring
  simp only [hpt]
  rw [avgR_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [avgR_const_mul]
  congr 1
  have hK := avgR_pair_pi (fun (_ : SubIdx) (c c' : ChildIdx × LutIdx) => ∑ T : Finset FChain,
    ∑ T' : Finset FChain, ((-1) ^ T.card * needA1 c.2 T) * ((-1) ^ T'.card * needA1 c'.2 T') *
      βf (decide (c.1 = c'.1)) c.2 T c'.2 T' ^ i)
  rw [hK, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show (avgR fun cc : (ChildIdx × LutIdx) × (ChildIdx × LutIdx) => ∑ T : Finset FChain, ∑ T' : Finset FChain,
      ((-1) ^ T.card * needA1 cc.1.2 T) * ((-1) ^ T'.card * needA1 cc.2.2 T') *
        βf (decide (cc.1.1 = cc.2.1)) cc.1.2 T cc.2.2 T' ^ i) = νR i from avg_child_pair i]

/-- **The second moment.** -/
theorem Ψ2R_eq (n : ℕ) :
    Ψ2R n = 1 / 16 * ∑ i ∈ Finset.range (n + 1), (1 / 16) ^ i * (15 / 16) ^ (n - i) * (n.choose i : ℝ) * νR i ^ 2 +
      15 / 16 * ∑ s ∈ Finset.range (n + 1), (1 / 16) ^ s * (14 / 16) ^ (n - s) * (n.choose s : ℝ) *
        ∑ i ∈ Finset.range (s + 1), (s.choose i : ℝ) * μR i ^ 2 * μR (s - i) ^ 2 := by
  rw [Ψ2R_signed]
  simp only [avgR_avoid2]
  rw [avgR_pair_prod_type]
  have h : ∀ ss : SuperIdx × SuperIdx, (avgR fun pp : (SubIdx → ChildIdx × LutIdx) × (SubIdx → ChildIdx × LutIdx) =>
      ∑ S : SubIdx → Finset FChain, ∑ S' : SubIdx → Finset FChain,
        (sgnS S * needA ((ss.1, pp.1), (ss.2, pp.2)).1 S) * (sgnS S' * needA ((ss.1, pp.1), (ss.2, pp.2)).2 S') *
          (if ((ss.1, pp.1), (ss.2, pp.2)).1.1 = ((ss.1, pp.1), (ss.2, pp.2)).2.1 then
            15 / 16 + 1 / 16 * ∏ j, βf (decide ((((ss.1, pp.1), (ss.2, pp.2)).1.2 j).1 =
              (((ss.1, pp.1), (ss.2, pp.2)).2.2 j).1)) (((ss.1, pp.1), (ss.2, pp.2)).1.2 j).2 (S j)
                (((ss.1, pp.1), (ss.2, pp.2)).2.2 j).2 (S' j)
          else 14 / 16 + 1 / 16 * (∏ j, (7 / 8 + 1 / 8 * G (((ss.1, pp.1), (ss.2, pp.2)).1.2 j).2 (S j))) +
            1 / 16 * ∏ j, (7 / 8 + 1 / 8 * G (((ss.1, pp.1), (ss.2, pp.2)).2.2 j).2 (S' j))) ^ n) =
      if ss.1 = ss.2 then ∑ i ∈ Finset.range (n + 1), (1 / 16) ^ i * (15 / 16) ^ (n - i) * (n.choose i : ℝ) * νR i ^ 2
      else ∑ s ∈ Finset.range (n + 1), (1 / 16) ^ s * (14 / 16) ^ (n - s) * (n.choose s : ℝ) *
        ∑ i ∈ Finset.range (s + 1), (s.choose i : ℝ) * μR i ^ 2 * μR (s - i) ^ 2 := by
    intro ss
    by_cases hs : ss.1 = ss.2
    · rw [if_pos hs, ← avg_eq_part n]
      refine congrArg avgR (funext fun pp => ?_)
      refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun S' _ => ?_
      rw [if_pos hs, needA_eq, needA_eq]
    · rw [if_neg hs, ← avg_ne_part n]
      refine congrArg avgR (funext fun pp => ?_)
      refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun S' _ => ?_
      rw [if_neg hs, needA_eq, needA_eq]
  simp only [h]
  rw [avgR_pair_ite]
  have hcard : (Fintype.card SuperIdx : ℝ) = 16 := by
    show (Fintype.card (Fin (2 ^ topHeight)) : ℝ) = 16
    rw [Fintype.card_fin]
    norm_num [topHeight]
  rw [hcard]
  ring

theorem νneR_eq (i : ℕ) :
    νneR i = ∑ s ∈ Finset.range (i + 1), (1 / 8) ^ s * (6 / 8) ^ (i - s) * (i.choose s : ℝ) *
      ∑ u ∈ Finset.range (s + 1), (s.choose u : ℝ) * fR u * fR (s - u) := by
  unfold νneR
  have hpt : ∀ ww : LutIdx × LutIdx, (∑ T : Finset FChain, ∑ T' : Finset FChain,
      ((-1) ^ T.card * needA1 ww.1 T) * ((-1) ^ T'.card * needA1 ww.2 T') * βf false ww.1 T ww.2 T' ^ i) =
      ∑ s ∈ Finset.range (i + 1), (1 / 8) ^ s * (6 / 8) ^ (i - s) * (i.choose s : ℝ) *
        ∑ u ∈ Finset.range (s + 1), (s.choose u : ℝ) * (∑ T : Finset FChain, (-1) ^ T.card * needA1 ww.1 T *
          G ww.1 T ^ u) * ∑ T' : Finset FChain, (-1) ^ T'.card * needA1 ww.2 T' * G ww.2 T' ^ (s - u) := by
    intro ww
    simp only [βf, Bool.false_eq_true, if_false]
    exact sum_sum_pow_affine2 _ _ _ _ _ _ _
  simp only [hpt]
  rw [avgR_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [avgR_const_mul, avgR_sum]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [show (fun ww : LutIdx × LutIdx => (s.choose u : ℝ) * (∑ T : Finset FChain, (-1) ^ T.card * needA1 ww.1 T *
      G ww.1 T ^ u) * ∑ T' : Finset FChain, (-1) ^ T'.card * needA1 ww.2 T' * G ww.2 T' ^ (s - u)) =
      fun ww => (s.choose u : ℝ) * ((fun w : LutIdx => ∑ T : Finset FChain, (-1) ^ T.card * needA1 w T *
        G w T ^ u) ww.1 * (fun w : LutIdx => ∑ T' : Finset FChain, (-1) ^ T'.card * needA1 w T' *
          G w T' ^ (s - u)) ww.2) from funext fun ww => by ring]
  rw [avgR_const_mul, avgR_prod_split (fun w : LutIdx => ∑ T : Finset FChain, (-1) ^ T.card * needA1 w T * G w T ^ u)
    (fun w : LutIdx => ∑ T' : Finset FChain, (-1) ^ T'.card * needA1 w T' * G w T' ^ (s - u))]
  unfold fR
  ring

theorem νeqR_eq (i : ℕ) :
    νeqR i = ∑ u ∈ Finset.range (i + 1), (1 / 8) ^ u * (7 / 8) ^ (i - u) * (i.choose u : ℝ) * f2R u := by
  unfold νeqR f2R
  have hpt : ∀ ww : LutIdx × LutIdx, (∑ T : Finset FChain, ∑ T' : Finset FChain,
      ((-1) ^ T.card * needA1 ww.1 T) * ((-1) ^ T'.card * needA1 ww.2 T') * βf true ww.1 T ww.2 T' ^ i) =
      ∑ u ∈ Finset.range (i + 1), (1 / 8) ^ u * (7 / 8) ^ (i - u) * (i.choose u : ℝ) *
        ∑ T : Finset FChain, ∑ T' : Finset FChain,
          ((-1) ^ T.card * needA1 ww.1 T) * ((-1) ^ T'.card * needA1 ww.2 T') * G2 ww.1 T ww.2 T' ^ u := by
    intro ww
    simp only [βf, if_true, pow_affine, Finset.mul_sum]
    have hsw : ∀ T : Finset FChain, (∑ T' : Finset FChain, ∑ u ∈ Finset.range (i + 1),
        ((-1) ^ T.card * needA1 ww.1 T) * ((-1) ^ T'.card * needA1 ww.2 T') *
          ((1 / 8) ^ u * (7 / 8) ^ (i - u) * (i.choose u : ℝ) * G2 ww.1 T ww.2 T' ^ u)) =
        ∑ u ∈ Finset.range (i + 1), ∑ T' : Finset FChain,
          ((-1) ^ T.card * needA1 ww.1 T) * ((-1) ^ T'.card * needA1 ww.2 T') *
            ((1 / 8) ^ u * (7 / 8) ^ (i - u) * (i.choose u : ℝ) * G2 ww.1 T ww.2 T' ^ u) := fun T => Finset.sum_comm
    simp only [hsw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun T' _ => ?_
    ring
  simp only [hpt]
  rw [avgR_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [avgR_const_mul]
end Sphincs.Security.H0
