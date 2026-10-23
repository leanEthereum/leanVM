import Sphincs.H0Bridge
import SphincsFors.H0Split

/-! **The forest H-term.** With per-index majorants `ḡ ≥ E[g(y) | n]` and `h̄ ≥ E[h(y) | n]` that
are increasing and convex in the number of views `n`, the separable count function
`Σ_l ḡ(k_l) + A Π_l h̄(k_l)` is a good count function; averaging out the marks and the Poisson
domination of the one-coin H-term give
`H ≤ L E_μ[ḡ] + A E_μ[h̄]^L`. -/

open ENNReal NNReal

namespace Sphincs.Security.H0

open Concrete ForestPrice SphincsFors.Security.Domination SphincsFors.Security.H0 H0Avg

set_option linter.unusedSectionVars false

/-! ### Separable good count functions -/

/-- Monotone, convex along every coordinate, finite, with at most exponential growth. -/
structure SepGood (g : ℕ → ℝ≥0∞) : Prop where
  mono : Monotone g
  convex : ∀ n, g (n + 1) + g (n + 1) ≤ g (n + 2) + g n
  growth : ∃ C : ℝ≥0, ∀ n, g n ≤ (C : ℝ≥0∞) * 2 ^ n

theorem SepGood.ne_top {g : ℕ → ℝ≥0∞} (hg : SepGood g) (n : ℕ) : g n ≠ ⊤ := by
  obtain ⟨C, hC⟩ := hg.growth
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top (by norm_num))) (hC n)

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
      simp only [eq_self_iff_true, ite_true, ite_eq_right hij, ite_eq_right (Ne.symm hij), add_zero]
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
        simp only [ite_true]
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
      simp only [eq_self_iff_true, ite_true]
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
      calc ∏ l, h (k l) ≤ ∏ l, (Ch : ℝ≥0∞) * 2 ^ k l := Finset.prod_le_prod fun l _ => hCh _
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

variable [Params]

/-- **The forest H-term.** -/
theorem hTermO_forest_le (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (N q : ℕ) (b0 : ℝ≥0∞) (c c1 θ : ℝ)
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
end Sphincs.Security.H0
