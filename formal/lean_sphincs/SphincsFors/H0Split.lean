import SphincsFors.H0Poisson

/-! The split majorant of the excess of the count price `Σ_l κ k_l^24` over a threshold. With
`y_l = κ k_l^24`, `m_l = min(y_l, c1)` and `M = Σ_l m_l`,
`(Σ_l y_l - β)^+ ≤ Σ_l (y_l - c1)^+ + (M - c)^+` for any real `c` with `c ≤ β`, and the last
term is bounded by the Chernoff majorant `e^{θ (M - c)} / (e θ) = e^{-θ c} / (e θ) Π_l e^{θ m_l}`.
The excess is a good count function, so the one-coin H-term is below its iid Poisson mean, which
factorizes over the leaves: `L E[(κ K^24 - c1)^+] + e^{-θ c} / (e θ) E[e^{θ min(κ K^24, c1)}]^L`. -/

open ENNReal NNReal

namespace SphincsFors.Security.H0

open Domination

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-! ### The excess as a count function -/

/-- The excess of the count price over `β`, as a function of the counts. -/
noncomputable def excessC (κ β : ℝ≥0∞) (k : ι → ℕ) : ℝ≥0∞ := (∑ l, κ * (k l : ℝ≥0∞) ^ 24) - β

/-- The real count price. -/
noncomputable def priceR (κ : ℝ) (k : ι → ℕ) : ℝ := ∑ l, κ * (k l : ℝ) ^ 24

theorem sum_price_ofReal (κ : ℝ≥0∞) (hκ : κ ≠ ⊤) (k : ι → ℕ) :
    ∑ l, κ * (k l : ℝ≥0∞) ^ 24 = ENNReal.ofReal (priceR κ.toReal k) := by
  unfold priceR
  rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hκ, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast]

theorem excessC_eq (κ β : ℝ≥0∞) (hκ : κ ≠ ⊤) (hβ : β ≠ ⊤) (k : ι → ℕ) :
    excessC κ β k = ENNReal.ofReal (priceR κ.toReal k - β.toReal) := by
  unfold excessC
  rw [sum_price_ofReal κ hκ, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hβ]

theorem priceR_mono {κ : ℝ} (hκ : 0 ≤ κ) {k k' : ι → ℕ} (h : k ≤ k') : priceR κ k ≤ priceR κ k' := by
  unfold priceR
  refine Finset.sum_le_sum fun l _ => ?_
  have : (k l : ℝ) ≤ k' l := by exact_mod_cast h l
  gcongr

theorem priceR_cross (κ : ℝ) (k : ι → ℕ) {i j : ι} (hij : i ≠ j) :
    priceR κ (k + Pi.single i 1 + Pi.single j 1) + priceR κ k =
      priceR κ (k + Pi.single i 1) + priceR κ (k + Pi.single j 1) := by
  unfold priceR
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases h1 : l = i
  · subst h1
    simp only [ite_eq_right hij]
    push_cast; ring
  · by_cases h2 : l = j
    · subst h2
      simp only [ite_eq_right h1]
      push_cast; ring
    · simp only [ite_eq_right h1, ite_eq_right h2]
      push_cast; ring

theorem pow24_convex (x : ℝ) (hx : 0 ≤ x) : 2 * (x + 1) ^ 24 ≤ (x + 2) ^ 24 + x ^ 24 := by
  have h := (convexOn_pow (𝕜 := ℝ) 24).2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ x + 2))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : 1 / 2 * x + 1 / 2 * (x + 2) = x + 1 := by ring
  rw [e] at h
  linarith

theorem priceR_convex {κ : ℝ} (hκ : 0 ≤ κ) (k : ι → ℕ) (i : ι) :
    2 * priceR κ (k + Pi.single i 1) ≤ priceR κ (k + Pi.single i 1 + Pi.single i 1) + priceR κ k := by
  unfold priceR
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases h1 : l = i
  · simp only [h1, ite_true]
    push_cast
    have := pow24_convex (k i : ℝ) (by positivity)
    have e : (k i : ℝ) + 1 + 1 = k i + 2 := by ring
    rw [e]
    nlinarith
  · simp [h1]
    nlinarith [show 0 ≤ κ * (k l : ℝ) ^ 24 by positivity]

/-- `ofReal a + ofReal b ≤ ofReal c + ofReal d` from the positive parts. -/
theorem ofReal_add_le_of_max {a b c d : ℝ} (h : max a 0 + max b 0 ≤ max c 0 + max d 0) :
    ENNReal.ofReal a + ENNReal.ofReal b ≤ ENNReal.ofReal c + ENNReal.ofReal d := by
  have e : ∀ x : ℝ, ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
    intro x
    rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx, ENNReal.ofReal_of_nonpos hx, ENNReal.ofReal_zero]
    · rw [max_eq_left hx]
  rw [e a, e b, e c, e d, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
  exact ENNReal.ofReal_le_ofReal h

/-- Increasing differences of the positive part. -/
theorem max_super (x y z w c : ℝ) (hy : x ≤ y) (hz : x ≤ z) (hw : y + z - x ≤ w) :
    max (y - c) 0 + max (z - c) 0 ≤ max (w - c) 0 + max (x - c) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

/-- **The excess is a good count function.** -/
theorem good_excessC (κ β : ℝ≥0∞) (hκ : κ ≠ ⊤) (hβ : β ≠ ⊤) : CountGood (excessC (ι := ι) κ β) where
  mono := fun k k' h => by
    rw [excessC_eq κ β hκ hβ, excessC_eq κ β hκ hβ]
    exact ENNReal.ofReal_le_ofReal (by linarith [priceR_mono (κ := κ.toReal) ENNReal.toReal_nonneg h])
  super := by
    intro k i j hij
    simp only [excessC_eq κ β hκ hβ]
    refine ofReal_add_le_of_max (max_super _ _ _ _ _ ?_ ?_ ?_)
    · exact priceR_mono ENNReal.toReal_nonneg le_self_add
    · exact priceR_mono ENNReal.toReal_nonneg le_self_add
    · linarith [priceR_cross κ.toReal k hij]
  convex := by
    intro k i
    simp only [excessC_eq κ β hκ hβ]
    refine ofReal_add_le_of_max (max_super _ _ _ _ _ ?_ ?_ ?_)
    · exact priceR_mono ENNReal.toReal_nonneg le_self_add
    · exact priceR_mono ENNReal.toReal_nonneg le_self_add
    · linarith [priceR_convex (κ := κ.toReal) ENNReal.toReal_nonneg k i]
  growth := by
    refine ⟨(Fintype.card ι : ℝ≥0) * κ.toNNReal, 2 ^ 24, fun k => ?_⟩
    unfold excessC
    refine le_trans tsub_le_self ?_
    have hk : ∀ l, (k l : ℝ≥0∞) ^ 24 ≤ ((2 : ℝ≥0∞) ^ 24) ^ (∑ i, k i) := by
      intro l
      have h1 : k l ≤ ∑ i, k i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ l)
      have h2 : k l ^ 24 ≤ (2 ^ 24) ^ (∑ i, k i) := by
        rw [← pow_mul, mul_comm, pow_mul]
        exact Nat.pow_le_pow_left (le_trans h1 Nat.lt_two_pow_self.le) 24
      exact_mod_cast h2
    calc ∑ l, κ * (k l : ℝ≥0∞) ^ 24 ≤ ∑ _l : ι, κ * ((2 : ℝ≥0∞) ^ 24) ^ (∑ i, k i) :=
          Finset.sum_le_sum fun l _ => mul_le_mul_right (hk l) κ
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal hκ]
          push_cast
          ring

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

/-- **Pointwise split majorant** of the excess, for any real `c` with `c ≤ β`. -/
theorem excessC_le_split (κ β : ℝ≥0∞) (hκ : κ ≠ ⊤) (c c1 θ : ℝ) (hc : ENNReal.ofReal c ≤ β) (hθ : 0 < θ)
    (k : ι → ℕ) :
    excessC κ β k ≤ ∑ l, ENNReal.ofReal (κ.toReal * (k l : ℝ) ^ 24 - c1) +
      ENNReal.ofReal (Real.exp (-θ * c) / (Real.exp 1 * θ)) *
        ∏ l, ENNReal.ofReal (Real.exp (θ * min (κ.toReal * (k l : ℝ) ^ 24) c1)) := by
  unfold excessC
  calc (∑ l, κ * (k l : ℝ≥0∞) ^ 24) - β ≤ (∑ l, κ * (k l : ℝ≥0∞) ^ 24) - ENNReal.ofReal c := tsub_le_tsub_left hc _
    _ ≤ ENNReal.ofReal (∑ l, κ.toReal * (k l : ℝ) ^ 24 - c) := by
        rw [sum_price_ofReal κ hκ]
        unfold priceR
        rcases le_total c 0 with h0 | h0
        · rw [ENNReal.ofReal_of_nonpos h0, tsub_zero]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        · rw [← ENNReal.ofReal_sub _ h0]
    _ ≤ ENNReal.ofReal (∑ l, max (κ.toReal * (k l : ℝ) ^ 24 - c1) 0 +
          Real.exp (-θ * c) / (Real.exp 1 * θ) * ∏ l, Real.exp (θ * min (κ.toReal * (k l : ℝ) ^ 24) c1)) :=
        ENNReal.ofReal_le_ofReal (split_real _ c c1 θ hθ)
    _ = _ := by
        rw [ENNReal.ofReal_add (Finset.sum_nonneg fun l _ => le_max_right _ _) (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun l _ => le_max_right _ _),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_prod_of_nonneg (fun l _ => by positivity)]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rcases le_total (κ.toReal * (k l : ℝ) ^ 24 - c1) 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
        · rw [max_eq_left h]

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
    simp only [ite_true, Pi.add_apply, Pi.single_eq_same]
    rfl
  · simp only [ite_eq_right hl, Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
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
    rw [ite_eq_right (Finset.ne_of_mem_erase hl)]
  unfold pois
  calc ∑' n, poisW a n * ∏ l, g l ((k + Pi.single j n : ι → ℕ) l)
      = ∑' n, poisW a n * g j (k j + n) * R := tsum_congr fun n => by rw [hterm n, mul_assoc]
    _ = pois1 a (g j) (k j) * R := by rw [ENNReal.tsum_mul_right]; rfl
    _ = _ := by rw [prod_split j, ite_eq_left rfl, hrest']

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
  simp only [Finset.mem_toList, Finset.mem_univ, ite_true, Pi.zero_apply, pois1_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

/-- Iid Poisson mean of a separable product: `E[g(K)]^L`. -/
theorem poisIID_sepProd (a : ℝ≥0) (g : ℕ → ℝ≥0∞) :
    poisIID a (fun x : ι → ℕ => ∏ l, g (x l)) 0 = poisMean a g ^ Fintype.card ι := by
  unfold poisIID
  rw [poisList_sepProd a _ (Finset.nodup_toList _) (fun _ => g)]
  simp only [Finset.mem_toList, Finset.mem_univ, ite_true, Pi.zero_apply, pois1_zero, Finset.prod_const,
    Finset.card_univ]

/-! ### The split bound of the one-coin H-term -/

/-- **Split bound of the one-coin H-term.** For any real `c ≤ β` (as `ofReal c ≤ β`), `c1` and
`θ > 0`, at any rate `μ ≥ N α + q γ`:
`H ≤ L E_μ[(κ K^24 - c1)^+] + e^{-θ c} / (e θ) E_μ[e^{θ min(κ K^24, c1)}]^L`. -/
theorem hTermO_split_le {V : Type} (idx : V → ι) (U : Finset V) (hU : UniformIndex idx U)
    (κ β : ℝ≥0∞) (hκ : κ ≠ ⊤) (hβ : β ≠ ⊤) (c c1 θ : ℝ) (hc : ENNReal.ofReal c ≤ β) (hθ : 0 < θ)
    (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (α γ : ℝ≥0) (hα : (Fintype.card ι : ℝ≥0∞) * α = 1)
    (hγ : (Fintype.card ι : ℝ≥0∞) * γ = lam * w) (N q : ℕ) (μ : ℝ≥0)
    (hμ : (N : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ) :
    hTermO U w lam N q (fun d => countPrice idx κ d - β) ≤
      (Fintype.card ι : ℝ≥0∞) * poisMean μ (fun n => ENNReal.ofReal (κ.toReal * (n : ℝ) ^ 24 - c1)) +
        ENNReal.ofReal (Real.exp (-θ * c) / (Real.exp 1 * θ)) *
          poisMean μ (fun n => ENNReal.ofReal (Real.exp (θ * min (κ.toReal * (n : ℝ) ^ 24) c1))) ^
            Fintype.card ι := by
  set h : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (κ.toReal * (n : ℝ) ^ 24 - c1) with hh
  set g : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (Real.exp (θ * min (κ.toReal * (n : ℝ) ^ 24) c1)) with hg
  set A := ENNReal.ofReal (Real.exp (-θ * c) / (Real.exp 1 * θ)) with hA
  have hF := good_excessC (ι := ι) κ β hκ hβ
  calc hTermO U w lam N q (fun d => countPrice idx κ d - β)
      = hTermO U w lam N q (fun d => excessC κ β (cnt idx d)) := rfl
    _ ≤ poisIID μ (excessC κ β) 0 := hTermO_le_poisIID_of_le idx U hU hF w lam hw hlam α γ hα hγ N q μ hμ
    _ ≤ poisIID μ (fun x => (fun x => ∑ l, h (x l)) x + A * (fun x => ∏ l, g (x l)) x) 0 :=
        poisList_mono μ _ (fun x => excessC_le_split κ β hκ c c1 θ hc hθ x) 0
    _ = _ := by
        unfold poisIID
        rw [poisList_add, poisList_const_mul]
        rw [← poisIID, ← poisIID, poisIID_sepSum, poisIID_sepProd]

end SphincsFors.Security.H0
