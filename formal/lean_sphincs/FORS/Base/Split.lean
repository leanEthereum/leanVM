import FORS.Base.Poisson

/-! The split majorant of the excess of a price `Σ_l y_l` over a threshold (for FORS, `y_l` is the
cover probability at index `l`, `excess_le_split`). With `m_l = min(y_l, c1)` and `M = Σ_l m_l`,
`(Σ_l y_l - β)^+ ≤ Σ_l (y_l - c1)^+ + (M - c)^+` for any real `c` with `c ≤ β`, and the last
term is bounded by the Chernoff majorant `e^{θ (M - c)} / (e θ) = e^{-θ c} / (e θ) Π_l e^{θ m_l}`.
Iid Poisson means of the separable sum and product factorize over the leaves:
`L E[g(K)]` and `E[h(K)]^L`. -/

open ENNReal NNReal

namespace FORS.Base.H0

open Domination

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-! ### The pointwise split majorant -/

/-- **Chernoff.** `M - c ≤ e^{-θ c} / (e θ) e^{θ M}` for `θ > 0`. -/
theorem chernoff_real (M c θ : ℝ) (hθ : 0 < θ) :
    M - c ≤ Real.exp (-θ * c) / (Real.exp 1 * θ) * Real.exp (θ * M) := by
  have h := Real.add_one_le_exp (θ * (M - c) - 1)
  have e : Real.exp (θ * (M - c) - 1) = Real.exp (-θ * c) * Real.exp (θ * M) / Real.exp 1 := by
    rw [Real.exp_sub, show θ * (M - c) = -θ * c + θ * M by ring, Real.exp_add]
  rw [e] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h1 : 0 < Real.exp 1 := Real.exp_pos 1
  rw [le_div_iff₀ h1] at h
  nlinarith

/-- The real split: `Σ y - c ≤ Σ (y - c1)^+ + e^{-θ c} / (e θ) Π e^{θ min(y, c1)}`. -/
theorem split_real (y : ι → ℝ) (c c1 θ : ℝ) (hθ : 0 < θ) :
    ∑ l, y l - c ≤ ∑ l, max (y l - c1) 0 +
      Real.exp (-θ * c) / (Real.exp 1 * θ) * ∏ l, Real.exp (θ * min (y l) c1) := by
  have hdec : ∑ l, y l = ∑ l, max (y l - c1) 0 + ∑ l, min (y l) c1 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [max_def, min_def]
    split_ifs <;> linarith
  have hch := chernoff_real (∑ l, min (y l) c1) c θ hθ
  rw [Finset.mul_sum, Real.exp_sum] at hch
  linarith

/-! ### The split by the number of big indices -/

/-- The `j`-th term of the split by the number of big indices: over the sets `T` of `j` indices, the
product of `[big l] e^{θ min(y_l, c1)}` on `T` and `e^{θ min(y_l, cap)}` off `T`. -/
noncomputable def splitTerm (y : ι → ℝ) (big : ι → Prop) [DecidablePred big] (c1 cap θ : ℝ) (j : ℕ) : ℝ :=
  ∑ T ∈ Finset.powersetCard j Finset.univ, ∏ l, if l ∈ T then (if big l then Real.exp (θ * min (y l) c1) else 0)
    else Real.exp (θ * min (y l) cap)

theorem splitTerm_nonneg (y : ι → ℝ) (big : ι → Prop) [DecidablePred big] (c1 cap θ : ℝ) (j : ℕ) :
    0 ≤ splitTerm y big c1 cap θ j :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by split_ifs <;> positivity

/-- A set `T` of big indices that holds every big index outside a cap `cap ≥ y`: the product is
`e^{θ Σ min(y, c1)}`. -/
theorem splitTerm_ge (y : ι → ℝ) (big : ι → Prop) [DecidablePred big] (c1 cap θ : ℝ) (T : Finset ι)
    (hT : ∀ l ∈ T, big l) (hout : ∀ l, l ∉ T → min (y l) cap = min (y l) c1) :
    Real.exp (θ * ∑ l, min (y l) c1) ≤ splitTerm y big c1 cap θ T.card := by
  unfold splitTerm
  have hmem : T ∈ Finset.powersetCard T.card Finset.univ :=
    Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun T' : Finset ι => ∏ l, if l ∈ T' then
    (if big l then Real.exp (θ * min (y l) c1) else 0) else Real.exp (θ * min (y l) cap))
    (fun _ _ => Finset.prod_nonneg fun _ _ => by split_ifs <;> positivity) hmem)
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun l _ => ?_
  by_cases hl : l ∈ T
  · rw [if_pos hl, if_pos (hT l hl)]
  · rw [if_neg hl, hout l hl]

/-- **The split by the number of big indices.** If every index that is not big has `y ≤ c2 ≤ c1`,
the excess is at most `Σ (y - c1)^+` plus, for `j ≤ m`, the Chernoff prefactor at `θ_j` times the
`j`-th term, with cap `c2` off the big set for `j < m` and `c1` for `j = m`: exactly `j < m` big
indices give `e^{θ_j M}` for the big set, at least `m` give it for any `m` of them. -/
theorem split_J (y : ι → ℝ) (big : ι → Prop) [DecidablePred big] (c c1 c2 : ℝ) (hc2 : c2 ≤ c1)
    (hsmall : ∀ l, ¬ big l → y l ≤ c2) (m : ℕ) (θ : ℕ → ℝ) (hθ : ∀ j ≤ m, 0 < θ j) :
    ∑ l, y l - c ≤ ∑ l, max (y l - c1) 0 +
      ∑ j ∈ Finset.range (m + 1), Real.exp (-θ j * c) / (Real.exp 1 * θ j) *
        splitTerm y big c1 (if j < m then c2 else c1) (θ j) j := by
  have hdec : ∑ l, y l = ∑ l, max (y l - c1) 0 + ∑ l, min (y l) c1 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [max_def, min_def]
    split_ifs <;> linarith
  set M := ∑ l, min (y l) c1
  have hterm : ∀ j ∈ Finset.range (m + 1), 0 ≤ Real.exp (-θ j * c) / (Real.exp 1 * θ j) *
      splitTerm y big c1 (if j < m then c2 else c1) (θ j) j := fun j hj =>
    mul_nonneg (div_nonneg (Real.exp_pos _).le (mul_pos (Real.exp_pos 1)
      (hθ j (by have := Finset.mem_range.1 hj; omega))).le) (splitTerm_nonneg _ _ _ _ _ _)
  -- one term of the sum bounds `M - c`
  obtain ⟨j, hj, hM⟩ : ∃ j ∈ Finset.range (m + 1), M - c ≤ Real.exp (-θ j * c) / (Real.exp 1 * θ j) *
      splitTerm y big c1 (if j < m then c2 else c1) (θ j) j := by
    set J := Finset.univ.filter big with hJ
    have hJbig : ∀ l ∈ J, big l := fun l hl => (Finset.mem_filter.1 hl).2
    rcases lt_or_ge J.card m with hlt | hge
    · refine ⟨J.card, Finset.mem_range.2 (by omega), ?_⟩
      have hge := splitTerm_ge y big c1 (if J.card < m then c2 else c1) (θ J.card) J hJbig (fun l hl => by
        rw [if_pos hlt]
        have hnb : ¬ big l := fun hb => hl (Finset.mem_filter.2 ⟨Finset.mem_univ l, hb⟩)
        have h1 := hsmall l hnb
        rw [min_eq_left h1, min_eq_left (le_trans h1 hc2)])
      exact le_trans (chernoff_real M c (θ J.card) (hθ _ hlt.le))
        (mul_le_mul_of_nonneg_left hge (div_nonneg (Real.exp_pos _).le (mul_pos (Real.exp_pos 1) (hθ _ hlt.le)).le))
    · obtain ⟨T, hTJ, hTc⟩ := Finset.exists_subset_card_eq hge
      refine ⟨m, Finset.mem_range.2 (by omega), ?_⟩
      have hge' := splitTerm_ge y big c1 (if m < m then c2 else c1) (θ m) T (fun l hl => hJbig l (hTJ hl))
        (fun l _ => by rw [if_neg (lt_irrefl m)])
      rw [hTc] at hge'
      exact le_trans (chernoff_real M c (θ m) (hθ _ le_rfl))
        (mul_le_mul_of_nonneg_left hge' (div_nonneg (Real.exp_pos _).le (mul_pos (Real.exp_pos 1) (hθ _ le_rfl)).le))
  have hsum := Finset.single_le_sum hterm hj
  linarith

/-! ### Iid Poisson means of separable sums and products -/

/-- One-coordinate Poisson mean `E[h(n + K)]`, `K ~ Poisson(a)`. -/
noncomputable def pois1 (a : ℝ≥0) (h : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ := ∑' m, poisW a m * h (n + m)

/-- The Poisson mean `E[h(K)]`, `K ~ Poisson(a)`. -/
noncomputable def poisMean (a : ℝ≥0) (h : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∑' m, poisW a m * h m

theorem pois1_zero (a : ℝ≥0) (h : ℕ → ℝ≥0∞) : pois1 a h 0 = poisMean a h := by
  simp [pois1, poisMean]

theorem pois_sepSum (a : ℝ≥0) (j : ι) (h : ι → ℕ → ℝ≥0∞) (k : ι → ℕ) :
    pois a j (fun x => ∑ l, h l (x l)) k = ∑ l, (if l = j then pois1 a (h l) (k l) else h l (k l)) := by
  unfold pois
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l = j
  · subst hl
    simp only [if_true, Pi.add_apply, Pi.single_eq_same]
    rfl
  · simp only [if_neg hl, Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
    rw [ENNReal.tsum_mul_right, poisW_tsum, one_mul]

theorem pois_sepProd (a : ℝ≥0) (j : ι) (g : ι → ℕ → ℝ≥0∞) (k : ι → ℕ) :
    pois a j (fun x => ∏ l, g l (x l)) k = ∏ l, (if l = j then pois1 a (g l) (k l) else g l (k l)) := by
  set R := ∏ l ∈ Finset.univ.erase j, g l (k l) with hR
  have hterm : ∀ n : ℕ, ∏ l, g l ((k + Pi.single j n : ι → ℕ) l) = g j (k j + n) * R := by
    intro n
    rw [prod_split j, hR]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun l hl => ?_
      rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hl), add_zero]
  have hrest' : ∏ l ∈ Finset.univ.erase j, (if l = j then pois1 a (g l) (k l) else g l (k l)) = R := by
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [if_neg (Finset.ne_of_mem_erase hl)]
  unfold pois
  calc ∑' n, poisW a n * ∏ l, g l ((k + Pi.single j n : ι → ℕ) l)
      = ∑' n, poisW a n * g j (k j + n) * R := tsum_congr fun n => by rw [hterm n, mul_assoc]
    _ = pois1 a (g j) (k j) * R := by rw [ENNReal.tsum_mul_right]; rfl
    _ = _ := by rw [prod_split j, if_pos rfl, hrest']

theorem poisList_sepSum (a : ℝ≥0) : ∀ (ls : List ι), ls.Nodup → ∀ (h : ι → ℕ → ℝ≥0∞) (k : ι → ℕ),
    poisList a ls (fun x => ∑ l, h l (x l)) k = ∑ l, (if l ∈ ls then pois1 a (h l) (k l) else h l (k l))
  | [], _, h, k => by simp [poisList]
  | j :: ls, hnd, h, k => by
      rw [List.nodup_cons] at hnd
      simp only [poisList]
      have e : pois a j (fun x => ∑ l, h l (x l)) =
          fun x => ∑ l, (fun l n => if l = j then pois1 a (h l) n else h l n) l (x l) := by
        funext x
        rw [pois_sepSum]
      rw [e]
      refine (poisList_sepSum a ls hnd.2 (fun l n => if l = j then pois1 a (h l) n else h l n) k).trans ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : l = j
      · subst hl
        simp [hnd.1]
      · by_cases hm : l ∈ ls
        · simp [hl, hm]
        · simp [hl, hm]

theorem poisList_sepProd (a : ℝ≥0) : ∀ (ls : List ι), ls.Nodup → ∀ (g : ι → ℕ → ℝ≥0∞) (k : ι → ℕ),
    poisList a ls (fun x => ∏ l, g l (x l)) k = ∏ l, (if l ∈ ls then pois1 a (g l) (k l) else g l (k l))
  | [], _, g, k => by simp [poisList]
  | j :: ls, hnd, g, k => by
      rw [List.nodup_cons] at hnd
      simp only [poisList]
      have e : pois a j (fun x => ∏ l, g l (x l)) =
          fun x => ∏ l, (fun l n => if l = j then pois1 a (g l) n else g l n) l (x l) := by
        funext x
        rw [pois_sepProd]
      rw [e]
      refine (poisList_sepProd a ls hnd.2 (fun l n => if l = j then pois1 a (g l) n else g l n) k).trans ?_
      refine Finset.prod_congr rfl fun l _ => ?_
      by_cases hl : l = j
      · subst hl
        simp [hnd.1]
      · by_cases hm : l ∈ ls
        · simp [hl, hm]
        · simp [hl, hm]

/-- Iid Poisson mean of a separable sum: `Σ_l E[h(K)]`. -/
theorem poisIID_sepSum (a : ℝ≥0) (h : ℕ → ℝ≥0∞) :
    poisIID a (fun x : ι → ℕ => ∑ l, h (x l)) 0 = (Fintype.card ι : ℝ≥0∞) * poisMean a h := by
  unfold poisIID
  rw [poisList_sepSum a _ (Finset.nodup_toList _) (fun _ => h)]
  simp only [Finset.mem_toList, Finset.mem_univ, if_true, Pi.zero_apply, pois1_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

/-- Iid Poisson mean of a separable product: `E[g(K)]^L`. -/
theorem poisIID_sepProd (a : ℝ≥0) (g : ℕ → ℝ≥0∞) :
    poisIID a (fun x : ι → ℕ => ∏ l, g (x l)) 0 = poisMean a g ^ Fintype.card ι := by
  unfold poisIID
  rw [poisList_sepProd a _ (Finset.nodup_toList _) (fun _ => g)]
  simp only [Finset.mem_toList, Finset.mem_univ, if_true, Pi.zero_apply, pois1_zero, Finset.prod_const,
    Finset.card_univ]

/-! ### Iid Poisson means of the terms of the split by big indices -/

theorem poisList_finset_sum (a : ℝ≥0) {α : Type} (s : Finset α) (G : α → (ι → ℕ) → ℝ≥0∞) (ls : List ι)
    (k : ι → ℕ) : poisList a ls (fun x => ∑ i ∈ s, G i x) k = ∑ i ∈ s, poisList a ls (G i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have h := poisList_const_mul a 0 ls (fun _ => 0) k
      simpa using h
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [poisList_add, ih]

/-- Iid Poisson mean of a product of per-coordinate functions: `Π_l E[g_l(K)]`. -/
theorem poisIID_prod (a : ℝ≥0) (g : ι → ℕ → ℝ≥0∞) :
    poisIID a (fun x : ι → ℕ => ∏ l, g l (x l)) 0 = ∏ l, poisMean a (g l) := by
  unfold poisIID
  rw [poisList_sepProd a _ (Finset.nodup_toList _) g]
  simp only [Finset.mem_toList, Finset.mem_univ, if_true, Pi.zero_apply, pois1_zero]

/-- **The iid Poisson mean of a term of the split**:
`Σ_{|T| = j} Π_{l ∈ T} E[f] Π_{l ∉ T} E[g] = C(L, j) E[f]^j E[g]^(L - j)`. -/
theorem poisIID_subsetProd (a : ℝ≥0) (j : ℕ) (f g : ℕ → ℝ≥0∞) :
    poisIID a (fun x : ι → ℕ => ∑ T ∈ Finset.powersetCard j Finset.univ,
      ∏ l, if l ∈ T then f (x l) else g (x l)) 0 =
      ((Fintype.card ι).choose j : ℝ≥0∞) * poisMean a f ^ j * poisMean a g ^ (Fintype.card ι - j) := by
  unfold poisIID
  rw [poisList_finset_sum]
  have hT : ∀ T ∈ Finset.powersetCard j (Finset.univ : Finset ι),
      poisList a (Finset.univ : Finset ι).toList (fun x : ι → ℕ => ∏ l, if l ∈ T then f (x l) else g (x l)) 0 =
        poisMean a f ^ j * poisMean a g ^ (Fintype.card ι - j) := by
    intro T hTm
    have hc := (Finset.mem_powersetCard.1 hTm).2
    rw [← poisIID]
    refine (poisIID_prod a (fun l n => if l ∈ T then f n else g n)).trans ?_
    have e2 : ∀ l, poisMean a (fun n => if l ∈ T then f n else g n) =
        if l ∈ T then poisMean a f else poisMean a g := fun l => by split_ifs <;> rfl
    simp only [e2]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    congr 2
    · rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hc]
    · rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff_of_subset
        (Finset.subset_univ _), Finset.card_univ, hc]
  rw [Finset.sum_congr rfl hT, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
  ring

end FORS.Base.H0
