import FORS.CoverBound.PerIndex

/-! **The FORS H-term.** With per-index majorants `ḡ ≥ E[g(y) | n]` and `h̄ ≥ E[h(y) | n]` that
are increasing and convex in the number of views `n`, the separable count function
`Σ_l ḡ(k_l) + A Π_l h̄(k_l)` is a good count function; averaging out the marks and the Poisson
domination of the one-coin H-term give
`H ≤ L E_μ[ḡ] + A E_μ[h̄]^L`. -/

open ENNReal NNReal

namespace FORS.Security.H0

variable [Params]

open Concrete ForsPrice FORS.Base.Domination FORS.Base.H0 H0Avg

set_option linter.unusedSectionVars false

/-! ### Separable good count functions -/

/-- Monotone, convex along every coordinate, finite, with at most exponential growth. -/
structure SepGood (g : ℕ → ℝ≥0∞) : Prop where
  mono : Monotone g
  convex : ∀ n, g (n + 1) + g (n + 1) ≤ g (n + 2) + g n
  growth : ∃ C : ℝ≥0, ∀ n, g n ≤ (C : ℝ≥0∞) * 2 ^ n

theorem cross_le {a a' b b' : ℝ≥0∞} (ha : a ≤ a') (hb : b ≤ b') :
    a' * b + a * b' ≤ a' * b' + a * b := by
  obtain ⟨δ, rfl⟩ := le_iff_exists_add.1 ha
  obtain ⟨ε, rfl⟩ := le_iff_exists_add.1 hb
  calc (a + δ) * b + a * (b + ε) = a * b + δ * b + a * b + a * ε := by ring
    _ ≤ a * b + δ * b + a * b + a * ε + δ * ε := le_self_add
    _ = _ := by ring

variable {ι : Type} [DecidableEq ι] [Fintype ι]

theorem prod_split_two (f : ι → ℝ≥0∞) {i j : ι} (hij : i ≠ j) :
    ∏ l, f l = f i * f j * ∏ l ∈ (Finset.univ.erase i).erase j, f l := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ j⟩), mul_assoc]

theorem prod_split_one (f : ι → ℝ≥0∞) (i : ι) : ∏ l, f l = f i * ∏ l ∈ Finset.univ.erase i, f l :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

/-- **Separable count functions are good.** -/
theorem sep_countGood {g h : ℕ → ℝ≥0∞} (hg : SepGood g) (hh : SepGood h) (A : ℝ≥0∞) (hA : A ≠ ⊤) :
    CountGood (fun k : ι → ℕ => ∑ l, g (k l) + A * ∏ l, h (k l)) where
  mono := by
    intro k k' hk
    simp only
    gcongr with l _ l _
    · exact hg.mono (hk l)
    · exact hh.mono (hk l)
  super := by
    intro k i j hij
    simp only [Pi.add_apply, Pi.single_apply]
    -- the sums
    have hsum : ∑ l, g (k l + if l = i then 1 else 0) + ∑ l, g (k l + if l = j then 1 else 0) =
        ∑ l, g (k l + (if l = i then 1 else 0) + if l = j then 1 else 0) + ∑ l, g (k l) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hi : l = i
      · subst hi; simp [hij]
      · by_cases hj : l = j
        · subst hj; simp [hi, add_comm]
        · simp [hi, hj]
    -- the products
    have hprod : (∏ l, h (k l + if l = i then 1 else 0)) + ∏ l, h (k l + if l = j then 1 else 0) ≤
        (∏ l, h (k l + (if l = i then 1 else 0) + if l = j then 1 else 0)) + ∏ l, h (k l) := by
      rw [prod_split_two _ hij, prod_split_two _ hij, prod_split_two _ hij, prod_split_two _ hij]
      have hR : ∀ (e : ι → ℕ), (∀ l, l ≠ i → l ≠ j → e l = k l) →
          ∏ l ∈ (Finset.univ.erase i).erase j, h (e l) = ∏ l ∈ (Finset.univ.erase i).erase j, h (k l) := by
        intro e he
        refine Finset.prod_congr rfl fun l hl => ?_
        have hl' := Finset.mem_erase.1 hl
        have hl'' := Finset.mem_erase.1 hl'.2
        rw [he l hl''.1 hl'.1]
      rw [hR (fun l => k l + if l = i then 1 else 0) (fun l hi hj => by simp [hi]),
        hR (fun l => k l + if l = j then 1 else 0) (fun l hi hj => by simp [hj]),
        hR (fun l => k l + (if l = i then 1 else 0) + if l = j then 1 else 0) (fun l hi hj => by simp [hi, hj])]
      simp only [if_true, if_neg hij, if_neg (Ne.symm hij), add_zero]
      set R := ∏ l ∈ (Finset.univ.erase i).erase j, h (k l)
      have hc := cross_le (hh.mono (Nat.le_succ (k i))) (hh.mono (Nat.le_succ (k j)))
      calc h (k i + 1) * h (k j) * R + h (k i) * h (k j + 1) * R =
            (h (k i + 1) * h (k j) + h (k i) * h (k j + 1)) * R := by ring
        _ ≤ (h (k i + 1) * h (k j + 1) + h (k i) * h (k j)) * R := mul_le_mul_left hc R
        _ = _ := by ring
    calc (∑ l, g (k l + if l = i then 1 else 0) + A * ∏ l, h (k l + if l = i then 1 else 0)) +
          (∑ l, g (k l + if l = j then 1 else 0) + A * ∏ l, h (k l + if l = j then 1 else 0)) =
        (∑ l, g (k l + if l = i then 1 else 0) + ∑ l, g (k l + if l = j then 1 else 0)) +
          A * ((∏ l, h (k l + if l = i then 1 else 0)) + ∏ l, h (k l + if l = j then 1 else 0)) := by ring
      _ ≤ (∑ l, g (k l + (if l = i then 1 else 0) + if l = j then 1 else 0) + ∑ l, g (k l)) +
          A * ((∏ l, h (k l + (if l = i then 1 else 0) + if l = j then 1 else 0)) + ∏ l, h (k l)) := by
        rw [hsum]
        exact add_le_add le_rfl (mul_le_mul_right hprod A)
      _ = _ := by ring
  convex := by
    intro k i
    simp only [Pi.add_apply, Pi.single_apply]
    have hsum : ∑ l, g (k l + if l = i then 1 else 0) + ∑ l, g (k l + if l = i then 1 else 0) ≤
        ∑ l, g (k l + (if l = i then 1 else 0) + if l = i then 1 else 0) + ∑ l, g (k l) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun l _ => ?_
      by_cases hi : l = i
      · subst hi
        simp only [if_true]
        exact hg.convex (k l)
      · simp [hi]
    have hprod : (∏ l, h (k l + if l = i then 1 else 0)) + ∏ l, h (k l + if l = i then 1 else 0) ≤
        (∏ l, h (k l + (if l = i then 1 else 0) + if l = i then 1 else 0)) + ∏ l, h (k l) := by
      rw [prod_split_one _ i, prod_split_one _ i, prod_split_one _ i]
      have hR : ∀ (e : ι → ℕ), (∀ l, l ≠ i → e l = k l) →
          ∏ l ∈ Finset.univ.erase i, h (e l) = ∏ l ∈ Finset.univ.erase i, h (k l) := by
        intro e he
        refine Finset.prod_congr rfl fun l hl => ?_
        rw [he l (Finset.mem_erase.1 hl).1]
      rw [hR (fun l => k l + if l = i then 1 else 0) (fun l hi => by simp [hi]),
        hR (fun l => k l + (if l = i then 1 else 0) + if l = i then 1 else 0) (fun l hi => by simp [hi])]
      simp only [if_true]
      set R := ∏ l ∈ Finset.univ.erase i, h (k l)
      calc h (k i + 1) * R + h (k i + 1) * R = (h (k i + 1) + h (k i + 1)) * R := by ring
        _ ≤ (h (k i + 2) + h (k i)) * R := mul_le_mul_left (hh.convex (k i)) R
        _ = _ := by ring
    calc (∑ l, g (k l + if l = i then 1 else 0) + A * ∏ l, h (k l + if l = i then 1 else 0)) +
          (∑ l, g (k l + if l = i then 1 else 0) + A * ∏ l, h (k l + if l = i then 1 else 0)) =
        (∑ l, g (k l + if l = i then 1 else 0) + ∑ l, g (k l + if l = i then 1 else 0)) +
          A * ((∏ l, h (k l + if l = i then 1 else 0)) + ∏ l, h (k l + if l = i then 1 else 0)) := by ring
      _ ≤ (∑ l, g (k l + (if l = i then 1 else 0) + if l = i then 1 else 0) + ∑ l, g (k l)) +
          A * ((∏ l, h (k l + (if l = i then 1 else 0) + if l = i then 1 else 0)) + ∏ l, h (k l)) :=
        add_le_add hsum (mul_le_mul_right hprod A)
      _ = _ := by ring
  growth := by
    obtain ⟨Cg, hCg⟩ := hg.growth
    obtain ⟨Ch, hCh⟩ := hh.growth
    refine ⟨Fintype.card ι * Cg + A.toNNReal * Ch ^ Fintype.card ι, 2, fun k => ?_⟩
    have hpow : ∀ l, (2 : ℝ≥0∞) ^ k l ≤ 2 ^ ∑ l', k l' := fun l =>
      pow_le_pow_right₀ (by norm_num) (Finset.single_le_sum (fun l' _ => Nat.zero_le (k l')) (Finset.mem_univ l))
    have h1 : ∑ l, g (k l) ≤ (Fintype.card ι : ℝ≥0∞) * Cg * 2 ^ ∑ l, k l := by
      calc ∑ l, g (k l) ≤ ∑ _l : ι, (Cg : ℝ≥0∞) * 2 ^ ∑ l', k l' :=
            Finset.sum_le_sum fun l _ => le_trans (hCg _) (mul_le_mul_right (hpow l) _)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    have h2 : ∏ l, h (k l) ≤ (Ch : ℝ≥0∞) ^ Fintype.card ι * 2 ^ ∑ l, k l := by
      calc ∏ l, h (k l) ≤ ∏ l, (Ch : ℝ≥0∞) * 2 ^ k l := Finset.prod_le_prod' fun l _ => hCh _
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow_eq_pow_sum]
    calc ∑ l, g (k l) + A * ∏ l, h (k l) ≤ (Fintype.card ι : ℝ≥0∞) * Cg * 2 ^ ∑ l, k l +
          A * ((Ch : ℝ≥0∞) ^ Fintype.card ι * 2 ^ ∑ l, k l) := add_le_add h1 (mul_le_mul_right h2 A)
      _ = ((Fintype.card ι * Cg + A.toNNReal * Ch ^ Fintype.card ι : ℝ≥0) : ℝ≥0∞) * ((2 : ℝ≥0) : ℝ≥0∞) ^ ∑ l, k l := by
        push_cast
        rw [ENNReal.coe_toNNReal hA]
        ring

theorem poisIID_sep (μ : ℝ≥0) (g h : ℕ → ℝ≥0∞) (A : ℝ≥0∞) :
    poisIID μ (fun k : ι → ℕ => ∑ l, g (k l) + A * ∏ l, h (k l)) 0 =
      (Fintype.card ι : ℝ≥0∞) * poisMean μ g + A * poisMean μ h ^ Fintype.card ι := by
  unfold poisIID
  rw [poisList_add, poisList_const_mul, ← poisIID, ← poisIID, poisIID_sepSum, poisIID_sepProd]

omit [DecidableEq ι] in
theorem uniformIndex_id [DecidableEq ι] : UniformIndex (id : ι → ι) Finset.univ := by
  intro g
  unfold freshAvg
  rw [Finset.card_univ]
  rfl

theorem cnt_id (e : Multiset ι) (l : ι) : cnt id e l = e.count l := by
  unfold cnt
  rw [Multiset.count_eq_card_filter_eq]
  congr 1
  exact Multiset.filter_congr fun x _ => by simp [eq_comm]

/-- **The FORS H-term.** -/
theorem hTermO_fors_le (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (N q : ℕ) (b0 : ℝ≥0∞) (c c1 θ : ℝ)
    (hc : ENNReal.ofReal c ≤ b0) (hθ : 0 < θ) (gbar hbar : ℕ → ℝ≥0∞) (hgG : SepGood gbar) (hhG : SepGood hbar)
    (hg : ∀ n, avgN (gS c1) n 0 ≤ gbar n) (hh : ∀ n, avgN (hS c1 θ) n 0 ≤ hbar n)
    (α γ : ℝ≥0) (hα : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * α = 1)
    (hγ : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * γ = lam * w) (μ : ℝ≥0)
    (hμ : (N : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ) :
    hTermO (Finset.univ : Finset View) w lam N q (ForsPotential.excess b0) ≤
      (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * poisMean μ gbar +
        ENNReal.ofReal (Real.exp (-θ * c) / (Real.exp 1 * θ)) * poisMean μ hbar ^ Fintype.card (Fin (2 ^ subtreeHeight)) := by
  set A := ENNReal.ofReal (Real.exp (-θ * c) / (Real.exp 1 * θ)) with hAdef
  have hdom : Dominated (ForsPotential.excess b0) (fun e : Multiset (Fin (2 ^ subtreeHeight)) =>
      ∑ l, gbar (e.count l) + A * ∏ l, hbar (e.count l)) :=
    dominated_of_split (gS c1) (hS c1 θ) A (fun d => excess_le_split b0 c c1 θ hc hθ d) gbar hbar hg hh
  refine le_trans (hTermO_le_of_dominated w lam N q hdom) ?_
  have hcnt : (fun e : Multiset (Fin (2 ^ subtreeHeight)) => ∑ l, gbar (e.count l) + A * ∏ l, hbar (e.count l)) =
      fun e => (fun k : Fin (2 ^ subtreeHeight) → ℕ => ∑ l, gbar (k l) + A * ∏ l, hbar (k l)) (cnt id e) := by
    funext e
    simp only [cnt_id]
  rw [hcnt]
  refine le_trans (hTermO_le_poisIID_of_le id Finset.univ uniformIndex_id
    (sep_countGood hgG hhG A ENNReal.ofReal_ne_top) w lam hw hlam α γ hα hγ N q μ hμ) (le_of_eq ?_)
  exact poisIID_sep μ gbar hbar A

/-! ### Count functions of the split by big indices -/

theorem countGood_add {G H : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (hH : CountGood H) :
    CountGood (fun k => G k + H k) where
  mono := fun k k' hk => add_le_add (hG.mono hk) (hH.mono hk)
  super := fun k i j hij => by
    have h1 := hG.super k i j hij
    have h2 := hH.super k i j hij
    calc G (k + Pi.single i 1) + H (k + Pi.single i 1) + (G (k + Pi.single j 1) + H (k + Pi.single j 1)) =
          (G (k + Pi.single i 1) + G (k + Pi.single j 1)) + (H (k + Pi.single i 1) + H (k + Pi.single j 1)) := by
          ring
      _ ≤ (G (k + Pi.single i 1 + Pi.single j 1) + G k) + (H (k + Pi.single i 1 + Pi.single j 1) + H k) :=
          add_le_add h1 h2
      _ = _ := by ring
  convex := fun k i => by
    have h1 := hG.convex k i
    have h2 := hH.convex k i
    calc G (k + Pi.single i 1) + H (k + Pi.single i 1) + (G (k + Pi.single i 1) + H (k + Pi.single i 1)) =
          (G (k + Pi.single i 1) + G (k + Pi.single i 1)) + (H (k + Pi.single i 1) + H (k + Pi.single i 1)) := by
          ring
      _ ≤ (G (k + Pi.single i 1 + Pi.single i 1) + G k) + (H (k + Pi.single i 1 + Pi.single i 1) + H k) :=
          add_le_add h1 h2
      _ = _ := by ring
  growth := by
    obtain ⟨C1, r1, h1⟩ := hG.growth
    obtain ⟨C2, r2, h2⟩ := hH.growth
    refine ⟨C1 + C2, r1 + r2, fun k => ?_⟩
    have p1 : (r1 : ℝ≥0∞) ^ (∑ l, k l) ≤ ((r1 + r2 : ℝ≥0) : ℝ≥0∞) ^ (∑ l, k l) :=
      pow_le_pow_left' (by exact_mod_cast le_self_add) _
    have p2 : (r2 : ℝ≥0∞) ^ (∑ l, k l) ≤ ((r1 + r2 : ℝ≥0) : ℝ≥0∞) ^ (∑ l, k l) :=
      pow_le_pow_left' (by exact_mod_cast le_add_self) _
    calc G k + H k ≤ (C1 : ℝ≥0∞) * (r1 : ℝ≥0∞) ^ (∑ l, k l) + (C2 : ℝ≥0∞) * (r2 : ℝ≥0∞) ^ (∑ l, k l) :=
          add_le_add (h1 k) (h2 k)
      _ ≤ (C1 : ℝ≥0∞) * ((r1 + r2 : ℝ≥0) : ℝ≥0∞) ^ (∑ l, k l) +
            (C2 : ℝ≥0∞) * ((r1 + r2 : ℝ≥0) : ℝ≥0∞) ^ (∑ l, k l) :=
          add_le_add (mul_le_mul_right p1 _) (mul_le_mul_right p2 _)
      _ = _ := by push_cast; ring

theorem countGood_const_mul {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    CountGood (fun k => c * G k) where
  mono := fun k k' hk => mul_le_mul_right (hG.mono hk) c
  super := fun k i j hij => by
    have h := mul_le_mul_right (hG.super k i j hij) c
    simpa only [mul_add] using h
  convex := fun k i => by
    have h := mul_le_mul_right (hG.convex k i) c
    simpa only [mul_add] using h
  growth := by
    obtain ⟨C, r, h⟩ := hG.growth
    refine ⟨c.toNNReal * C, r, fun k => ?_⟩
    calc c * G k ≤ c * ((C : ℝ≥0∞) * (r : ℝ≥0∞) ^ (∑ l, k l)) := mul_le_mul_right (h k) c
      _ = _ := by push_cast; rw [ENNReal.coe_toNNReal hc]; ring

theorem countGood_zero : CountGood (fun _ : ι → ℕ => (0 : ℝ≥0∞)) where
  mono := fun _ _ _ => le_rfl
  super := fun _ _ _ _ => by simp
  convex := fun _ _ => by simp
  growth := ⟨0, 0, fun _ => by simp⟩

theorem countGood_finset_sum {α : Type} (s : Finset α) (G : α → (ι → ℕ) → ℝ≥0∞)
    (h : ∀ i ∈ s, CountGood (G i)) : CountGood (fun k => ∑ i ∈ s, G i k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (countGood_zero : CountGood (fun _ : ι → ℕ => (0 : ℝ≥0∞)))
  | insert i s hi ih =>
      have e : (fun k => ∑ x ∈ insert i s, G x k) = fun k => G i k + ∑ x ∈ s, G x k := by
        funext k; rw [Finset.sum_insert hi]
      rw [e]
      exact countGood_add (h i (Finset.mem_insert_self i s)) (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

/-- Separable sums are good. -/
theorem sum_countGood {g : ℕ → ℝ≥0∞} (hg : SepGood g) : CountGood (fun k : ι → ℕ => ∑ l, g (k l)) := by
  have h := sep_countGood (ι := ι) hg hg 0 ENNReal.zero_ne_top
  simpa only [zero_mul, add_zero] using h

/-- **Products of per-coordinate good functions are good.** -/
theorem prod_countGood (g : ι → ℕ → ℝ≥0∞) (hg : ∀ l, SepGood (g l)) :
    CountGood (fun k : ι → ℕ => ∏ l, g l (k l)) where
  mono := by
    intro k k' hk
    exact Finset.prod_le_prod' fun l _ => (hg l).mono (hk l)
  super := by
    intro k i j hij
    simp only [Pi.add_apply, Pi.single_apply]
    rw [prod_split_two _ hij, prod_split_two _ hij, prod_split_two _ hij, prod_split_two _ hij]
    have hR : ∀ (e : ι → ℕ), (∀ l, l ≠ i → l ≠ j → e l = k l) →
        ∏ l ∈ (Finset.univ.erase i).erase j, g l (e l) = ∏ l ∈ (Finset.univ.erase i).erase j, g l (k l) := by
      intro e he
      refine Finset.prod_congr rfl fun l hl => ?_
      have hl' := Finset.mem_erase.1 hl
      have hl'' := Finset.mem_erase.1 hl'.2
      rw [he l hl''.1 hl'.1]
    rw [hR (fun l => k l + if l = i then 1 else 0) (fun l hi hj => by simp [hi]),
      hR (fun l => k l + if l = j then 1 else 0) (fun l hi hj => by simp [hj]),
      hR (fun l => k l + (if l = i then 1 else 0) + if l = j then 1 else 0) (fun l hi hj => by simp [hi, hj])]
    simp only [if_true, if_neg hij, if_neg (Ne.symm hij), add_zero]
    set R := ∏ l ∈ (Finset.univ.erase i).erase j, g l (k l)
    have hc := cross_le ((hg i).mono (Nat.le_succ (k i))) ((hg j).mono (Nat.le_succ (k j)))
    calc g i (k i + 1) * g j (k j) * R + g i (k i) * g j (k j + 1) * R =
          (g i (k i + 1) * g j (k j) + g i (k i) * g j (k j + 1)) * R := by ring
      _ ≤ (g i (k i + 1) * g j (k j + 1) + g i (k i) * g j (k j)) * R := mul_le_mul_left hc R
      _ = _ := by ring
  convex := by
    intro k i
    simp only [Pi.add_apply, Pi.single_apply]
    rw [prod_split_one _ i, prod_split_one _ i, prod_split_one _ i]
    have hR : ∀ (e : ι → ℕ), (∀ l, l ≠ i → e l = k l) →
        ∏ l ∈ Finset.univ.erase i, g l (e l) = ∏ l ∈ Finset.univ.erase i, g l (k l) := by
      intro e he
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [he l (Finset.mem_erase.1 hl).1]
    rw [hR (fun l => k l + if l = i then 1 else 0) (fun l hi => by simp [hi]),
      hR (fun l => k l + (if l = i then 1 else 0) + if l = i then 1 else 0) (fun l hi => by simp [hi])]
    simp only [if_true]
    set R := ∏ l ∈ Finset.univ.erase i, g l (k l)
    calc g i (k i + 1) * R + g i (k i + 1) * R = (g i (k i + 1) + g i (k i + 1)) * R := by ring
      _ ≤ (g i (k i + 2) + g i (k i)) * R := mul_le_mul_left ((hg i).convex (k i)) R
      _ = _ := by ring
  growth := by
    choose C hC using fun l => (hg l).growth
    refine ⟨∏ l, C l, 2, fun k => ?_⟩
    calc ∏ l, g l (k l) ≤ ∏ l, (C l : ℝ≥0∞) * 2 ^ k l := Finset.prod_le_prod' fun l _ => hC l _
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
          push_cast
          rfl

/-- The count function of the split by big indices, `Σ_l ḡ(k_l) + Σ_j A_j Σ_{|T| = j} Π_{l ∈ T} ā_j(k_l)
Π_{l ∉ T} h̄_j(k_l)`, is good. -/
theorem splitJ_countGood {g : ℕ → ℝ≥0∞} (hg : SepGood g) (S : Finset ℕ) (A : ℕ → ℝ≥0∞) (hA : ∀ j ∈ S, A j ≠ ⊤)
    (a h : ℕ → ℕ → ℝ≥0∞) (ha : ∀ j ∈ S, SepGood (a j)) (hh : ∀ j ∈ S, SepGood (h j)) :
    CountGood (fun k : ι → ℕ => ∑ l, g (k l) + ∑ j ∈ S, A j * ∑ T ∈ Finset.powersetCard j Finset.univ,
      ∏ l, if l ∈ T then a j (k l) else h j (k l)) := by
  refine countGood_add (sum_countGood hg) (countGood_finset_sum S _ fun j hj => ?_)
  refine countGood_const_mul ?_ (A j) (hA j hj)
  refine countGood_finset_sum _ _ fun T _ => ?_
  have e : (fun k : ι → ℕ => ∏ l, if l ∈ T then a j (k l) else h j (k l)) =
      fun k => ∏ l, (fun l n => if l ∈ T then a j n else h j n) l (k l) := rfl
  rw [e]
  refine prod_countGood (fun l n => if l ∈ T then a j n else h j n) fun l => ?_
  by_cases hl : l ∈ T
  · simp only [hl, if_true]; exact ha j hj
  · simp only [hl, if_false]; exact hh j hj

theorem poisIID_splitJ (μ : ℝ≥0) (g : ℕ → ℝ≥0∞) (S : Finset ℕ) (A : ℕ → ℝ≥0∞) (a h : ℕ → ℕ → ℝ≥0∞) :
    poisIID μ (fun k : ι → ℕ => ∑ l, g (k l) + ∑ j ∈ S, A j * ∑ T ∈ Finset.powersetCard j Finset.univ,
      ∏ l, if l ∈ T then a j (k l) else h j (k l)) 0 =
      (Fintype.card ι : ℝ≥0∞) * poisMean μ g + ∑ j ∈ S, A j * (((Fintype.card ι).choose j : ℝ≥0∞) *
        poisMean μ (a j) ^ j * poisMean μ (h j) ^ (Fintype.card ι - j)) := by
  unfold poisIID
  rw [poisList_add, ← poisIID, poisIID_sepSum, poisList_finset_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [poisList_const_mul, ← poisIID, poisIID_subsetProd]

/-! ### Averaging the marks of the split by big indices -/

theorem avgL_finset_sum {M : Type} [Fintype M] [Nonempty M] {α : Type} (s : Finset α)
    (f : α → Multiset (ι × M) → ℝ≥0∞) (L : List ι) (d0 : Multiset (ι × M)) :
    avgL (fun d => ∑ i ∈ s, f i d) L d0 = ∑ i ∈ s, avgL (f i) L d0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have h := avgL_const_mul (ι := ι) (M := M) 0 (fun _ => 0) L d0
      simpa using h
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [avgL_add, ih]

/-- **Domination by the count function of the split by big indices.** -/
theorem dominated_of_splitJ {M : Type} [Fintype M] [Nonempty M] {f : Multiset (ι × M) → ℝ≥0∞}
    (g : Multiset M → ℝ≥0∞) (S : Finset ℕ) (A : ℕ → ℝ≥0∞) (a h : ℕ → Multiset M → ℝ≥0∞)
    (hf : ∀ d, f d ≤ ∑ l, g (marksAt l d) + ∑ j ∈ S, A j * ∑ T ∈ Finset.powersetCard j Finset.univ,
      ∏ l, if l ∈ T then a j (marksAt l d) else h j (marksAt l d))
    (gbar : ℕ → ℝ≥0∞) (abar hbar : ℕ → ℕ → ℝ≥0∞) (hg : ∀ n, avgN g n 0 ≤ gbar n)
    (ha : ∀ j ∈ S, ∀ n, avgN (a j) n 0 ≤ abar j n) (hh : ∀ j ∈ S, ∀ n, avgN (h j) n 0 ≤ hbar j n) :
    Dominated f (fun e => ∑ l, gbar (e.count l) + ∑ j ∈ S, A j * ∑ T ∈ Finset.powersetCard j Finset.univ,
      ∏ l, if l ∈ T then abar j (e.count l) else hbar j (e.count l)) := by
  intro L
  refine le_trans (avgL_mono hf L 0) ?_
  rw [avgL_add, avgL_sum_marks (fun _ => g), avgL_finset_sum]
  simp only [marksAt_zero, Multiset.coe_count]
  refine add_le_add (Finset.sum_le_sum fun l _ => hg _) (Finset.sum_le_sum fun j hj => ?_)
  rw [avgL_const_mul, avgL_finset_sum]
  refine mul_le_mul_right (Finset.sum_le_sum fun T _ => ?_) _
  rw [avgL_prod_marks (fun l Ms => if l ∈ T then a j Ms else h j Ms)]
  simp only [marksAt_zero]
  refine Finset.prod_le_prod' fun l _ => ?_
  by_cases hl : l ∈ T
  · simp only [hl, if_true]; exact ha j hj _
  · simp only [hl, if_false]; exact hh j hj _

/-! ### The FORS H-term by the number of big indices -/

/-- The per-index factor of a big index (more than `nb` views) in the split by big indices. -/
noncomputable def aS (c1 θ : ℝ) (nb : ℕ) (Ms : Multiset (FTree → FLeaf)) : ℝ≥0∞ :=
  if nb < Ms.card then hS c1 θ Ms else 0

/-- The Chernoff prefactor `e^{-θ c} / (e θ)`. -/
noncomputable def prefR (θ c : ℝ) : ℝ := Real.exp (-θ * c) / (Real.exp 1 * θ)

/-- **The pointwise split by big indices** of the excess of the FORS price: an index with at most
`nb` views has `y ≤ c2`. -/
theorem excess_le_splitJ (b0 : ℝ≥0∞) (c c1 c2 : ℝ) (hc : ENNReal.ofReal c ≤ b0) (hc2 : c2 ≤ c1) (nb : ℕ)
    (hsmall : ∀ Ms : Multiset (FTree → FLeaf), Ms.card ≤ nb → κE.toReal * (yM Ms).toReal ≤ c2)
    (m : ℕ) (θ : ℕ → ℝ) (hθ : ∀ j ≤ m, 0 < θ j) (d : Multiset View) :
    ForsPotential.excess b0 d ≤ ∑ l : Fin (2 ^ subtreeHeight), gS c1 (marksAt l d) +
      ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (prefR (θ j) c) *
        ∑ T ∈ Finset.powersetCard j Finset.univ, ∏ l : Fin (2 ^ subtreeHeight),
          if l ∈ T then aS c1 (θ j) nb (marksAt l d) else hS (if j < m then c2 else c1) (θ j) (marksAt l d) := by
  unfold ForsPotential.excess
  rw [price_decomp]
  set y : Fin (2 ^ subtreeHeight) → ℝ := fun l => κE.toReal * (yM (marksAt l d)).toReal with hy
  have hsum : ∑ l : Fin (2 ^ subtreeHeight), (landing * (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞)⁻¹) *
      yM (marksAt l d) = ENNReal.ofReal (∑ l, y l) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hy, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal κE_ne_top,
      ENNReal.ofReal_toReal (yM_ne_top _)]
    rfl
  rw [hsum]
  have hsplit := FORS.Base.H0.split_J y (fun l => nb < (marksAt l d).card) c c1 c2 hc2
    (fun l hl => hsmall _ (not_lt.1 hl)) m θ hθ
  have hpref : ∀ j ∈ Finset.range (m + 1), 0 ≤ prefR (θ j) c := fun j hj =>
    div_nonneg (Real.exp_pos _).le (mul_pos (Real.exp_pos 1) (hθ j (by have := Finset.mem_range.1 hj; omega))).le
  calc ENNReal.ofReal (∑ l, y l) - b0 ≤ ENNReal.ofReal (∑ l, y l) - ENNReal.ofReal c := tsub_le_tsub_left hc _
    _ ≤ ENNReal.ofReal (∑ l, y l - c) := by
        rcases le_total c 0 with h0 | h0
        · rw [ENNReal.ofReal_of_nonpos h0, tsub_zero]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        · rw [← ENNReal.ofReal_sub _ h0]
    _ ≤ ENNReal.ofReal (∑ l, max (y l - c1) 0 + ∑ j ∈ Finset.range (m + 1), prefR (θ j) c *
          FORS.Base.H0.splitTerm y (fun l => nb < (marksAt l d).card) c1 (if j < m then c2 else c1) (θ j) j) :=
        ENNReal.ofReal_le_ofReal hsplit
    _ = _ := by
        rw [ENNReal.ofReal_add (Finset.sum_nonneg fun l _ => le_max_right _ _)
          (Finset.sum_nonneg fun j hj => mul_nonneg (hpref j hj) (FORS.Base.H0.splitTerm_nonneg _ _ _ _ _ _)),
          ENNReal.ofReal_sum_of_nonneg (fun l _ => le_max_right _ _),
          ENNReal.ofReal_sum_of_nonneg (fun j hj => mul_nonneg (hpref j hj) (FORS.Base.H0.splitTerm_nonneg _ _ _ _ _ _))]
        congr 1
        · refine Finset.sum_congr rfl fun l _ => ?_
          unfold gS
          rcases le_total (y l - c1) 0 with h | h
          · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
          · rw [max_eq_left h]
        · refine Finset.sum_congr rfl fun j hj => ?_
          unfold FORS.Base.H0.splitTerm
          rw [ENNReal.ofReal_mul (hpref j hj), ENNReal.ofReal_sum_of_nonneg (fun T _ =>
            Finset.prod_nonneg fun l _ => by split_ifs <;> positivity)]
          congr 1
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => by split_ifs <;> positivity)]
          refine Finset.prod_congr rfl fun l _ => ?_
          unfold aS hS
          split_ifs <;> simp [hy]

/-- **The FORS H-term by big indices.** -/
theorem hTermO_fors_leJ (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (N q : ℕ) (b0 : ℝ≥0∞) (c c1 c2 : ℝ)
    (hc : ENNReal.ofReal c ≤ b0) (hc2 : c2 ≤ c1) (nb : ℕ)
    (hsmall : ∀ Ms : Multiset (FTree → FLeaf), Ms.card ≤ nb → κE.toReal * (yM Ms).toReal ≤ c2)
    (m : ℕ) (θ : ℕ → ℝ) (hθ : ∀ j ≤ m, 0 < θ j)
    (gbar : ℕ → ℝ≥0∞) (abar hbar : ℕ → ℕ → ℝ≥0∞) (hgG : SepGood gbar)
    (haG : ∀ j ∈ Finset.range (m + 1), SepGood (abar j)) (hhG : ∀ j ∈ Finset.range (m + 1), SepGood (hbar j))
    (hg : ∀ n, avgN (gS c1) n 0 ≤ gbar n)
    (ha : ∀ j ∈ Finset.range (m + 1), ∀ n, avgN (aS c1 (θ j) nb) n 0 ≤ abar j n)
    (hh : ∀ j ∈ Finset.range (m + 1), ∀ n, avgN (hS (if j < m then c2 else c1) (θ j)) n 0 ≤ hbar j n)
    (α γ : ℝ≥0) (hα : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * α = 1)
    (hγ : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * γ = lam * w) (μ : ℝ≥0)
    (hμ : (N : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ) :
    hTermO (Finset.univ : Finset View) w lam N q (ForsPotential.excess b0) ≤
      (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * poisMean μ gbar +
        ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (prefR (θ j) c) *
          (((Fintype.card (Fin (2 ^ subtreeHeight))).choose j : ℝ≥0∞) * poisMean μ (abar j) ^ j *
            poisMean μ (hbar j) ^ (Fintype.card (Fin (2 ^ subtreeHeight)) - j)) := by
  set S := Finset.range (m + 1)
  set A : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (prefR (θ j) c) with hAdef
  have hdom : Dominated (ForsPotential.excess b0) (fun e : Multiset (Fin (2 ^ subtreeHeight)) =>
      ∑ l, gbar (e.count l) + ∑ j ∈ S, A j * ∑ T ∈ Finset.powersetCard j Finset.univ,
        ∏ l, if l ∈ T then abar j (e.count l) else hbar j (e.count l)) :=
    dominated_of_splitJ (gS c1) S A (fun j => aS c1 (θ j) nb) (fun j => hS (if j < m then c2 else c1) (θ j))
      (fun d => excess_le_splitJ b0 c c1 c2 hc hc2 nb hsmall m θ hθ d) gbar abar hbar hg ha hh
  refine le_trans (hTermO_le_of_dominated w lam N q hdom) ?_
  have hcnt : (fun e : Multiset (Fin (2 ^ subtreeHeight)) => ∑ l, gbar (e.count l) + ∑ j ∈ S, A j *
      ∑ T ∈ Finset.powersetCard j Finset.univ, ∏ l, if l ∈ T then abar j (e.count l) else hbar j (e.count l)) =
      fun e => (fun k : Fin (2 ^ subtreeHeight) → ℕ => ∑ l, gbar (k l) + ∑ j ∈ S, A j *
        ∑ T ∈ Finset.powersetCard j Finset.univ, ∏ l, if l ∈ T then abar j (k l) else hbar j (k l)) (cnt id e) := by
    funext e
    simp only [cnt_id]
  rw [hcnt]
  refine le_trans (hTermO_le_poisIID_of_le id Finset.univ uniformIndex_id
    (splitJ_countGood hgG S A (fun _ _ => ENNReal.ofReal_ne_top) abar hbar haG hhG) w lam hw hlam α γ hα hγ N q μ hμ)
    (le_of_eq ?_)
  exact poisIID_splitJ μ gbar S A abar hbar

end FORS.Security.H0
