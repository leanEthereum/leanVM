import Sphincs.H0Bridge

/-! **The near moment.** A target is *half covered* at tree `c`, subtree `j`, when every chain of the
WOTS key it selects in subtree `j` of tree `c` is opened deep enough. Its probability over `n`
uniform marks is `ΨH(n) = Σ_k C(n,k) (1/16)^k (15/16)^(n-k) μ_k`, by the inclusion-exclusion of the
first per-tree moment restricted to one subtree. The near witness of a target, summed over the free
subtree `(c, j)`, has per-index mean `Σ_{c,j} Ψ1(n)^7 ΨH(n)`. -/

open ENNReal

namespace Sphincs.Security.H0

open Concrete H0Avg SphincsFors.Security.Domination

set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-! ### One subtree, as tuples -/

/-- Every chain of subtree `j` that the target needs is opened deep enough. -/
def CoverHT (t : MT) (j : SubIdx) (X : Multiset MT) : Prop := ∀ i, need t j i = 0 ∨ ∃ x ∈ X, KC x t j i

/-- The half-cover indicator as a real number. -/
noncomputable def coverHR (t : MT) (j : SubIdx) (X : Multiset MT) : ℝ := by
  classical
  exact if CoverHT t j X then 1 else 0

/-- A choice of chains in subtree `j` only. -/
def single (j : SubIdx) (T : Finset FChain) : SubIdx → Finset FChain := fun j' => if j' = j then T else ∅

theorem prod_single {β : Type} [CommMonoid β] (j : SubIdx) (g : SubIdx → β) (hg : ∀ j', j' ≠ j → g j' = 1) :
    ∏ j', g j' = g j := by
  rw [Finset.prod_eq_single j (fun j' _ hj' => hg j' hj') (fun h => absurd (Finset.mem_univ j) h)]

theorem sgnS_single (j : SubIdx) (T : Finset FChain) : sgnS (single j T) = (-1) ^ T.card := by
  unfold sgnS
  rw [prod_single j _ (fun j' hj' => by simp [single, hj'])]
  simp [single]

theorem needA_single (t : MT) (j : SubIdx) (T : Finset FChain) :
    needA t (single j T) = needA1 (t.2 j).2 T := by
  unfold needA needA1
  rw [prod_single j _ (fun j' hj' => by simp [single, hj'])]
  simp only [single, if_true]
  rfl

theorem avoidB_single (t : MT) (j : SubIdx) (T : Finset FChain) (x : MT) :
    avoidB t (single j T) x = ∏ i ∈ T, (1 - if KC x t j i then (1 : ℝ) else 0) := by
  classical
  unfold avoidB
  rw [prod_single j _ (fun j' hj' => by simp [single, hj'])]
  simp only [single, if_true]

theorem coverHR_eq_prod (t : MT) (j : SubIdx) (X : Multiset MT) :
    coverHR t j X = ∏ i, (1 - (if need t j i = 0 then 0 else 1) *
      (X.map fun x => (1 - if KC x t j i then (1 : ℝ) else 0)).prod) := by
  classical
  have hpt : ∀ i, (1 - (if need t j i = 0 then (0 : ℝ) else 1) *
      (X.map fun x => (1 - if KC x t j i then (1 : ℝ) else 0)).prod) =
      if need t j i = 0 ∨ ∃ x ∈ X, KC x t j i then 1 else 0 := by
    intro i
    by_cases h0 : need t j i = 0
    · rw [if_pos h0, zero_mul, sub_zero, if_pos (Or.inl h0)]
    · rw [if_neg h0, one_mul]
      by_cases hx : ∃ x ∈ X, KC x t j i
      · obtain ⟨x, hx, hk⟩ := hx
        rw [if_pos (Or.inr ⟨x, hx, hk⟩), Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨x, hx, by simp [hk]⟩),
          sub_zero]
      · push Not at hx
        rw [if_neg (by rintro (h | ⟨x, hx', hk⟩); exact h0 h; exact hx x hx' hk)]
        rw [Multiset.prod_eq_one (fun y hy => by
          obtain ⟨x, hx', rfl⟩ := Multiset.mem_map.1 hy
          simp [hx x hx'])]
        ring
  simp only [hpt]
  unfold coverHR CoverHT
  by_cases hc : ∀ i, need t j i = 0 ∨ ∃ x ∈ X, KC x t j i
  · rw [if_pos hc]
    symm
    exact Finset.prod_eq_one fun i _ => if_pos (hc i)
  · rw [if_neg hc]
    push Not at hc
    obtain ⟨i, hi⟩ := hc
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [if_neg]
    rintro (h | ⟨x, hx, hk⟩)
    · exact hi.1 h
    · exact hi.2 x hx hk

/-- **Inclusion-exclusion of the half-cover indicator.** -/
theorem coverHR_expand (t : MT) (j : SubIdx) (X : Multiset MT) :
    coverHR t j X = ∑ T : Finset FChain, sgnS (single j T) * needA t (single j T) *
      (X.map (avoidB t (single j T))).prod := by
  classical
  rw [coverHR_eq_prod, prod_one_sub_mul]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [sgnS_single, needA_single]
  have hav : avoidB t (single j T) = fun x => ∏ i ∈ T, (1 - if KC x t j i then (1 : ℝ) else 0) :=
    funext fun x => avoidB_single t j T x
  have hn : needA1 (t.2 j).2 T = ∏ i ∈ T, if need t j i = 0 then (0 : ℝ) else 1 := rfl
  rw [hav, multiset_prod_finset_prod, hn]

/-- The half-cover moment. -/
noncomputable def ΨHR (j : SubIdx) (n : ℕ) : ℝ :=
  avgNR (fun X : Multiset MT => avgR fun t : MT => coverHR t j X) n 0

theorem G_empty (w : LutIdx) : G w ∅ = 1 := by
  unfold G
  simp only [Finset.prod_empty]
  exact avgR_const 1

theorem avgR_avoidB_single (t : MT) (j : SubIdx) (T : Finset FChain) :
    avgR (avoidB t (single j T)) = 15 / 16 + 1 / 16 * (7 / 8 + 1 / 8 * G (t.2 j).2 T) := by
  rw [avgR_avoidB]
  congr 2
  rw [prod_single j _ (fun j' hj' => by simp [single, hj', G_empty]; norm_num)]
  simp [single]

theorem ΨHR_signed (j : SubIdx) (n : ℕ) :
    ΨHR j n = avgR fun t : MT => ∑ T : Finset FChain, sgnS (single j T) * needA t (single j T) *
      avgR (avoidB t (single j T)) ^ n := by
  unfold ΨHR
  rw [avgNR_avgR]
  refine congrArg avgR (funext fun t => ?_)
  have hc : coverHR t j = fun X => ∑ T : Finset FChain,
      sgnS (single j T) * needA t (single j T) * (X.map (avoidB t (single j T))).prod :=
    funext fun X => coverHR_expand t j X
  rw [hc, avgNR_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [avgNR_const_mul, avgNR_prod_map, Multiset.map_zero, Multiset.prod_zero, one_mul]

/-- Averages of a function of one subtree's codeword. -/
theorem avgR_word (j : SubIdx) (g : LutIdx → ℝ) : avgR (fun t : MT => g (t.2 j).2) = avgR g := by
  calc avgR (fun t : MT => g (t.2 j).2) = avgR (fun w : SubIdx → LutIdx => g (w j)) :=
        avgR_words (fun w => g (w j))
    _ = avgR (fun w : SubIdx → LutIdx => ∏ j', (if j' = j then g (w j') else (1 : ℝ))) := by
        refine congrArg avgR (funext fun w => ?_)
        rw [prod_single j _ (fun j' hj' => by simp only [if_neg hj'])]
        simp
    _ = ∏ j', avgR (fun x : LutIdx => if j' = j then g x else (1 : ℝ)) :=
        avgR_prod_pi (fun j' (x : LutIdx) => if j' = j then g x else (1 : ℝ))
    _ = avgR g := by
        rw [prod_single j _ (fun j' hj' => by simp only [if_neg hj']; exact avgR_const 1)]
        simp

/-- **The half-cover moment.** -/
theorem ΨHR_eq (j : SubIdx) (n : ℕ) :
    ΨHR j n = ∑ k ∈ Finset.range (n + 1), (1 / 16) ^ k * (15 / 16) ^ (n - k) * (n.choose k : ℝ) * μR k := by
  rw [ΨHR_signed]
  simp only [avgR_avoidB_single, sgnS_single, needA_single]
  rw [avgR_word j (fun w => ∑ T : Finset FChain, (-1) ^ T.card * needA1 w T *
    (15 / 16 + 1 / 16 * (7 / 8 + 1 / 8 * G w T)) ^ n)]
  have hexp : ∀ w : LutIdx, (∑ T : Finset FChain, (-1) ^ T.card * needA1 w T *
      (15 / 16 + 1 / 16 * (7 / 8 + 1 / 8 * G w T)) ^ n) =
      ∑ k ∈ Finset.range (n + 1), (1 / 16) ^ k * (15 / 16) ^ (n - k) * (n.choose k : ℝ) *
        ∑ T : Finset FChain, (-1) ^ T.card * needA1 w T * (1 / 8 * G w T + 7 / 8) ^ k := by
    intro w
    simp only [pow_affine (15 / 16 : ℝ) (1 / 16 : ℝ), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun T _ => ?_
    have h78 : (7 / 8 + 1 / 8 * G w T : ℝ) = 1 / 8 * G w T + 7 / 8 := by ring
    rw [h78]
    ring
  simp only [hexp]
  rw [avgR_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [avgR_const_mul]
  rfl

/-! ### One subtree, as fields -/

/-- Every chain the target field needs in subtree `j` is opened deep enough by a disclosed field. -/
def CoverHF (t : FieldVal) (j : SubIdx) (Xs : Multiset FieldVal) : Prop :=
  ∀ i, chainNeed t j i = 0 ∨ ∃ x ∈ Xs, KeyCovers x t j i

theorem coverHF_iff (t : FieldVal) (j : SubIdx) (Xs : Multiset FieldVal) :
    CoverHF t j Xs ↔ CoverHT (fieldMT t) j (Xs.map fieldMT) := by
  unfold CoverHF CoverHT
  simp only [Multiset.mem_map]
  constructor
  · intro h i
    rcases h i with h0 | ⟨x, hx, hk⟩
    · exact Or.inl h0
    · exact Or.inr ⟨fieldMT x, ⟨x, hx, rfl⟩, hk⟩
  · intro h i
    rcases h i with h0 | ⟨_, ⟨x, hx, rfl⟩, hk⟩
    · exact Or.inl h0
    · exact Or.inr ⟨x, hx, hk⟩

open Classical in
/-- The per-tree half-cover fraction. -/
noncomputable def φH (j : SubIdx) (Xs : Multiset FieldVal) : ℝ≥0∞ :=
  freshAvg Finset.univ fun t : FieldVal => if CoverHF t j Xs then 1 else 0

theorem coverHR_nonneg (t : MT) (j : SubIdx) (X : Multiset MT) : 0 ≤ coverHR t j X := by
  unfold coverHR; split_ifs <;> norm_num

theorem coverHAvg_nonneg (j : SubIdx) (X : Multiset MT) : 0 ≤ avgR fun t : MT => coverHR t j X := by
  unfold avgR
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun t _ => coverHR_nonneg t j X)

theorem φH_eq (j : SubIdx) (Xs : Multiset FieldVal) :
    φH j Xs = ENNReal.ofReal (avgR fun t : MT => coverHR t j (Xs.map fieldMT)) := by
  classical
  unfold φH
  have hpt : ∀ t : FieldVal, (if CoverHF t j Xs then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal (coverHR (fieldMT t) j (Xs.map fieldMT)) := by
    intro t
    unfold coverHR
    by_cases h : CoverHF t j Xs
    · rw [if_pos h, if_pos ((coverHF_iff t j Xs).1 h), ENNReal.ofReal_one]
    · rw [if_neg h, if_neg (fun h' => h ((coverHF_iff t j Xs).2 h')), ENNReal.ofReal_zero]
  simp only [hpt]
  rw [freshAvg_ofReal _ (fun t => coverHR_nonneg _ _ _), avgR_equiv fieldMT]
  simp only [Equiv.apply_symm_apply]

theorem avgN_φH (j : SubIdx) (n : ℕ) : avgN (φH j) n 0 = ENNReal.ofReal (ΨHR j n) := by
  rw [avgN_field (φH j) (fun X => avgR fun t : MT => coverHR t j X) (coverHAvg_nonneg j) (φH_eq j) n 0]
  rfl

theorem φH_le_one (j : SubIdx) (Xs : Multiset FieldVal) : φH j Xs ≤ 1 := by
  classical
  unfold φH
  calc freshAvg Finset.univ (fun t : FieldVal => if CoverHF t j Xs then (1 : ℝ≥0∞) else 0)
      ≤ freshAvg Finset.univ (fun _ : FieldVal => (1 : ℝ≥0∞)) :=
        freshAvg_mono _ fun t _ => by split_ifs <;> simp
    _ = 1 := by rw [freshAvg_const _ Finset.univ_nonempty]

/-! ### The near value of an index -/

/-- The per-tree factor of the near value: the half cover at the free tree, the cover elsewhere. -/
noncomputable def nearFactor (c : Coord) (j : SubIdx) (c' : Coord) : Multiset FieldVal → ℝ≥0∞ :=
  if c' = c then φH j else φF

/-- **The near value of a multiset of disclosed marks at one index.** -/
noncomputable def yN (Ms : Multiset (Coord → FieldVal)) : ℝ≥0∞ :=
  ∑ c, ∑ j, ∏ c', nearFactor c j c' (Ms.map fun m => m c')

theorem avgN_sum_fin {U : Type} [Fintype U] [Nonempty U] {β : Type} [DecidableEq β] (s : Finset β)
    (φ : β → Multiset U → ℝ≥0∞) (n : ℕ) (X : Multiset U) :
    avgN (fun Y => ∑ b ∈ s, φ b Y) n X = ∑ b ∈ s, avgN (φ b) n X := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact avgN_const 0 n X
  | insert b s hb ih =>
      have h1 : (fun Y => ∑ b' ∈ insert b s, φ b' Y) = fun Y => φ b Y + ∑ b' ∈ s, φ b' Y :=
        funext fun Y => Finset.sum_insert hb
      rw [h1, avgN_add, ih, Finset.sum_insert hb]

/-- **`E[near | n] = Σ_{c,j} Ψ1(n)^7 ΨH(n)`.** -/
theorem avgN_yN (n : ℕ) :
    avgN yN n 0 = ∑ _c : Coord, ∑ j : SubIdx, ENNReal.ofReal (ΨHR j n) * ENNReal.ofReal (Ψ1R n) ^ 7 := by
  unfold yN
  rw [avgN_sum_fin]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [avgN_sum_fin]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [avgN_prod_coords (nearFactor c j) n 0]
  simp only [Multiset.map_zero]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
  have h1 : avgN (nearFactor c j c) n 0 = ENNReal.ofReal (ΨHR j n) := by
    simp only [nearFactor, if_true]; exact avgN_φH j n
  have h2 : ∀ c' ∈ Finset.univ.erase c, avgN (nearFactor c j c') n 0 = ENNReal.ofReal (Ψ1R n) := by
    intro c' hc'
    simp only [nearFactor, if_neg (Finset.ne_of_mem_erase hc')]
    exact avgN_φF n
  rw [h1, Finset.prod_congr rfl h2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, card_coord]

theorem yN_le (Ms : Multiset (Coord → FieldVal)) : yN Ms ≤ 16 := by
  unfold yN
  calc ∑ c, ∑ j, ∏ c', nearFactor c j c' (Ms.map fun m => m c') ≤ ∑ _c : Coord, ∑ _j : SubIdx, (1 : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun j _ => ?_
        refine Finset.prod_le_one' fun c' _ => ?_
        unfold nearFactor
        split_ifs
        · exact φH_le_one j _
        · exact φF_le_one _
    _ = 16 := by
        simp only [Finset.sum_const, Finset.card_univ, card_coord, nsmul_eq_mul, mul_one]
        norm_num

end Sphincs.Security.H0
