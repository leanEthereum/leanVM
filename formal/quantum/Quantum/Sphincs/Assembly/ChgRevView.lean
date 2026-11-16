module

public import Quantum.Xmss.Assembly.CwRev

@[expose] public section

/-!
# The view lemma with pairs of undisclosed sources

CwRev's view lemma (`sum_queryWeight_view_le_wt`) names one undisclosed source per input state.
The cross-message collisions of leanSPHINCS's digest labels are events on two undisclosed
randomizers at once; here the view lemma takes the count over the families agreeing on the label
as a hypothesis, and that count is supplied for pairs of sources.

* `card_mul_sum_agree_mem₂`: counting along two distinct undisclosed coordinates.
* `sum_agree_and_le₂`: if every family with `P` has a pair `j` of undisclosed sources with its
  values in `F j u` (not depending on `u` at the pair), the families agreeing with `v` on `T`
  with `P` are at most `κ` times all of them, `κ` bounding `∑ⱼ |F j u| / (|D s₁| |D s₂|)`.
* `sum_totalWeight_le_cnt`: the adaptive view lemma with a count hypothesis per input state,
  summed over the calls.
-/

universe u v w u₁ v₁

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

namespace Quantum.Sphincs.Assembly

open Quantum QuantumRuntime Quantum.Xmss.Hybrid
open Quantum.Xmss.Assembly (kWt)

/-! ## Counting along pairs of sources -/

section pairs

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)]

/-- **Counting along two undisclosed coordinates.** For distinct `s₁, s₂ ∉ T` and sets `F u` of
pairs that do not depend on `u` at `s₁` or `s₂`, the families agreeing with `v` on `T` whose pair
of values lies in `F u` are a `|D s₁| |D s₂|`-th of the weighted count `∑ |F u|`. -/
theorem card_mul_sum_agree_mem₂ (T : Finset S) (v : (s : S) → D s) {s₁ s₂ : S} (h₁ : s₁ ∉ T)
    (h₂ : s₂ ∉ T) (hne : s₁ ≠ s₂) (F : ((s : S) → D s) → Finset (D s₁ × D s₂))
    (hF₁ : ∀ u d, F (Function.update u s₁ d) = F u)
    (hF₂ : ∀ u d, F (Function.update u s₂ d) = F u) :
    ((Fintype.card (D s₁) : ℝ≥0∞) * Fintype.card (D s₂)) *
        ∑ u, (if Agree T v u ∧ (u s₁, u s₂) ∈ F u then 1 else 0) =
      ∑ u, if Agree T v u then ((F u).card : ℝ≥0∞) else 0 := by
  classical
  set G : ((s : S) → D s) → Finset (D s₂) := fun u ↦ Finset.univ.filter fun d ↦ (u s₁, d) ∈ F u
    with hG
  have hG₂ : ∀ u d, G (Function.update u s₂ d) = G u := fun u d ↦ by
    simp only [hG, hF₂, Function.update_of_ne hne]
  have hmem : ∀ u, ((u s₁, u s₂) ∈ F u) ↔ u s₂ ∈ G u := fun u ↦ by simp [hG]
  have e2 := card_mul_sum_agree_mem T v h₂ G hG₂
  have hfib : ∀ u, ∑ d : D s₁, ((G (Function.update u s₁ d)).card : ℝ≥0∞) = (F u).card := by
    intro u
    have h' : ∀ d : D s₁, G (Function.update u s₁ d) = Finset.univ.filter fun d₂ ↦ (d, d₂) ∈ F u :=
      fun d ↦ by simp only [hG, hF₁, Function.update_self]
    simp only [h']
    have hc : (F u).card = ∑ p : D s₁ × D s₂, if p ∈ F u then 1 else 0 := by
      rw [← Finset.card_filter]
      congr 1
      ext p
      simp
    rw [hc, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [Finset.card_filter]
    push_cast
    rfl
  have e1 : (Fintype.card (D s₁) : ℝ≥0∞) *
      ∑ u, (if Agree T v u then ((G u).card : ℝ≥0∞) else 0) =
      ∑ u, if Agree T v u then ((F u).card : ℝ≥0∞) else 0 := by
    rw [← sum_sum_update s₁]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    simp only [agree_update_iff h₁]
    by_cases h : Agree T v u
    · simp only [h, ↓reduceIte]
      exact hfib u
    · simp [h]
  rw [mul_assoc, ← e1, ← e2]
  congr 2
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  simp only [hmem]

/-- **The count of a family of pairs of sources.** If every family `u` with `P u` has a pair `j`
of undisclosed sources whose values lie in `F j u` (which depends on `u` at neither source), the
families agreeing with `v` on `T` with `P` are at most `κ` times all those agreeing with `v` on
`T`, where `κ` bounds `∑ⱼ |F j u| / (|D (s₁ j)| |D (s₂ j)|)`. A pair with equal sources has no
values. -/
theorem sum_agree_and_le₂ [∀ s, Nonempty (D s)] (T : Finset S) (v : (s : S) → D s)
    (P : ((s : S) → D s) → Prop) [DecidablePred P] {ι : Type} [Fintype ι] (s₁ s₂ : ι → S)
    (F : (j : ι) → ((s : S) → D s) → Finset (D (s₁ j) × D (s₂ j)))
    (hne : ∀ j, s₁ j = s₂ j → ∀ u, F j u = ∅)
    (hF₁ : ∀ j u d, F j (Function.update u (s₁ j) d) = F j u)
    (hF₂ : ∀ j u d, F j (Function.update u (s₂ j) d) = F j u)
    (hP : ∀ u, P u → ∃ j, s₁ j ∉ T ∧ s₂ j ∉ T ∧ (u (s₁ j), u (s₂ j)) ∈ F j u) (κ : ℝ≥0∞)
    (hκ : ∀ u, ∑ j, ((F j u).card : ℝ≥0∞) *
      ((Fintype.card (D (s₁ j)) : ℝ≥0∞) * Fintype.card (D (s₂ j)))⁻¹ ≤ κ) :
    ∑ u, (if Agree T v u ∧ P u then (1 : ℝ≥0∞) else 0) ≤
      κ * ∑ u, if Agree T v u then 1 else 0 := by
  classical
  set J : Finset ι := Finset.univ.filter fun j ↦ s₁ j ∉ T ∧ s₂ j ∉ T with hJ
  have hc : ∀ j, ((Fintype.card (D (s₁ j)) : ℝ≥0∞) * Fintype.card (D (s₂ j))) ≠ 0 := fun j ↦
    mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have ht : ∀ j, ((Fintype.card (D (s₁ j)) : ℝ≥0∞) * Fintype.card (D (s₂ j))) ≠ ⊤ := fun j ↦
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)
  calc ∑ u, (if Agree T v u ∧ P u then (1 : ℝ≥0∞) else 0)
      ≤ ∑ u, ∑ j ∈ J, (if Agree T v u ∧ (u (s₁ j), u (s₂ j)) ∈ F j u then 1 else 0) := by
        refine Finset.sum_le_sum fun u _ ↦ ?_
        split_ifs with h
        · obtain ⟨j, hj1, hj2, hjF⟩ := hP u h.2
          refine le_trans ?_ (Finset.single_le_sum
            (f := fun j ↦ if Agree T v u ∧ (u (s₁ j), u (s₂ j)) ∈ F j u then (1 : ℝ≥0∞)
              else 0)
            (fun _ _ ↦ by simp) (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj1, hj2⟩))
          simp [h.1, hjF]
        · simp
    _ = ∑ j ∈ J, ∑ u, (if Agree T v u ∧ (u (s₁ j), u (s₂ j)) ∈ F j u then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ j ∈ J, ((Fintype.card (D (s₁ j)) : ℝ≥0∞) * Fintype.card (D (s₂ j)))⁻¹ *
          ∑ u, (if Agree T v u then ((F j u).card : ℝ≥0∞) else 0) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        obtain ⟨-, hj1, hj2⟩ := Finset.mem_filter.mp hj
        by_cases he : s₁ j = s₂ j
        · simp [hne j he]
        rw [← card_mul_sum_agree_mem₂ T v hj1 hj2 he (F j) (hF₁ j) (hF₂ j), ← mul_assoc,
          ENNReal.inv_mul_cancel (hc j) (ht j), one_mul]
    _ = ∑ u, ∑ j ∈ J, ((Fintype.card (D (s₁ j)) : ℝ≥0∞) * Fintype.card (D (s₂ j)))⁻¹ *
          (if Agree T v u then ((F j u).card : ℝ≥0∞) else 0) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ u, if Agree T v u then ∑ j ∈ J, ((F j u).card : ℝ≥0∞) *
          ((Fintype.card (D (s₁ j)) : ℝ≥0∞) * Fintype.card (D (s₂ j)))⁻¹ else 0 := by
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        by_cases h : Agree T v u
        · simp only [h, ↓reduceIte]
          exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
        · simp [h]
    _ ≤ ∑ u, if Agree T v u then κ else 0 := by
        refine Finset.sum_le_sum fun u _ ↦ ?_
        split_ifs
        · exact (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans (hκ u)
        · exact le_rfl
    _ = κ * ∑ u, if Agree T v u then 1 else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        split_ifs <;> simp

end pairs

/-! ## The view lemma with a count per input state -/

section view

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)]

open scoped Classical in
/-- **The pointwise count with a count hypothesis** (CwRev's `sum_agree_diagMass_le_wt` with the
count over the agreeing families as a hypothesis). -/
theorem sum_agree_diagMass_le_cnt {α : Type} [Fintype α]
    (lab : α → Finset S) (T : Finset S) (v : (s : S) → D s) (C : ((s : S) → D s) → Set α)
    (κ : α → ℝ≥0∞)
    (hcnt : ∀ a, lab a = T → ∑ u, (if Agree T v u ∧ a ∈ C u then (1 : ℝ≥0∞) else 0) ≤
      κ a * ∑ u, if Agree T v u then 1 else 0) (σ : Matrix α α ℂ) :
    ∑ u, (if Agree T v u then diagMass (C u ∩ {a | lab a = T}) σ else 0) ≤
      (∑ u, if Agree T v u then (1 : ℝ≥0∞) else 0) *
        kWt (fun a ↦ if lab a = T then κ a else 0) σ := by
  simp only [diagMass, kWt]
  rw [Finset.mul_sum]
  calc ∑ u, (if Agree T v u then
          ∑ a, (C u ∩ {a | lab a = T}).indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a else 0)
      = ∑ a, ∑ u, (if Agree T v u then
          (C u ∩ {a | lab a = T}).indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        split_ifs <;> simp
    _ ≤ _ := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        by_cases ha : lab a = T
        · calc ∑ u, (if Agree T v u then
                  (C u ∩ {a | lab a = T}).indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a else 0)
              = ENNReal.ofReal (σ a a).re *
                  ∑ u, (if Agree T v u ∧ a ∈ C u then (1 : ℝ≥0∞) else 0) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun u _ ↦ ?_
                by_cases h1 : Agree T v u <;> by_cases h2 : a ∈ C u <;>
                  simp [h1, h2, ha]
            _ ≤ ENNReal.ofReal (σ a a).re *
                  (κ a * ∑ u, if Agree T v u then (1 : ℝ≥0∞) else 0) := by
                gcongr
                exact hcnt a ha
            _ = _ := by rw [ite_eq_left ha]; ring
        · rw [ite_eq_right ha, zero_mul, mul_zero]
          refine le_of_eq (Finset.sum_eq_zero fun u _ ↦ ?_)
          split_ifs
          · exact Set.indicator_of_notMem (fun h ↦ ha h.2) _
          · rfl

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

open scoped Classical in
/-- **The view lemma at one label with a count hypothesis.** -/
theorem sum_queryWeight_cut_le_cnt [∀ s, Nonempty (D s)] (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (P : spec.Port → Prop) (hview : ViewByOn R I P lab x ρ j)
    (C : ((s : S) → D s) → ∀ i, Set (spec.In i × R.D)) (hCP : ∀ v i, ¬ P i → C v i = ∅)
    (κ : ∀ i, spec.In i × R.D → ℝ≥0∞)
    (hcnt : ∀ v i p, ∑ u, (if Agree (lab p.2) v u ∧ p ∈ C u i then (1 : ℝ≥0∞) else 0) ≤
      κ i p * ∑ u, if Agree (lab p.2) v u then 1 else 0) (T : Finset S) :
    ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v) (ρ v) j ≤
      ∑ v, R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ i p else 0))
        (x v) (ρ v) j := by
  obtain ⟨v₀⟩ : Nonempty ((s : S) → D s) := inferInstance
  set N : ℝ≥0∞ := ∑ u, if Agree T v₀ u then 1 else 0 with hN
  have hNv : ∀ v, ∑ u, (if Agree T v u then (1 : ℝ≥0∞) else 0) = N :=
    fun v ↦ sum_agree_eq T v v₀
  have hN1 : 1 ≤ N := by
    have h := Finset.single_le_sum (f := fun u ↦ if Agree T v₀ u then (1 : ℝ≥0∞) else 0)
      (fun _ _ ↦ by simp) (Finset.mem_univ v₀)
    simp only [show Agree T v₀ v₀ from fun _ _ ↦ rfl, ↓reduceIte] at h
    exact h
  have hN0 : N ≠ 0 := (zero_lt_one.trans_le hN1).ne'
  have hNtop : N ≠ ⊤ := by
    rw [hN]
    exact ENNReal.sum_ne_top.mpr fun u _ ↦ by split_ifs <;> simp
  have hv : ∀ v, ∑ u, (if Agree T v u then
      R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j else 0) ≤
        N * R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ i p else 0))
          (x v) (ρ v) j := by
    intro v
    have hstep : ∀ u, (if Agree T v u then
        R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j else 0) =
          R.queryWeight I (fun i σ ↦ if Agree T v u then
            diagMass (C u i ∩ {p | lab p.2 = T}) σ else 0) (x v) (ρ v) j := by
      intro u
      by_cases h : Agree T v u
      · simp only [h, ↓reduceIte]
        exact (hview T v u h (fun i ↦ C u i ∩ {p | lab p.2 = T}) (fun i p hp ↦ hp.2)
          fun i hi ↦ by rw [hCP u i hi, Set.empty_inter]).symm
      · simp only [h, ↓reduceIte]
        exact (queryWeight_zero_weight R I (x v) (ρ v) j).symm
    simp only [hstep]
    rw [← queryWeight_fintype_sum, ← R.queryWeight_const_mul]
    refine R.queryWeight_mono I (fun i σ _ ↦ ?_) (x v) (hρ v) j
    have h := sum_agree_diagMass_le_cnt (fun p : spec.In i × R.D ↦ lab p.2) T v (fun u ↦ C u i)
      (κ i) (fun p hp ↦ by rw [← hp]; exact hcnt v i p) σ
    rwa [hNv v] at h
  have h1 : N * ∑ u, R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u)
      (ρ u) j = ∑ v, ∑ u, (if Agree T v u then
        R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j
          else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [← hNv u, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    have hs : Agree T u v ↔ Agree T v u := ⟨Agree.symm, Agree.symm⟩
    by_cases h : Agree T v u <;> simp [h, hs]
  have h2 : N * ∑ u, R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u)
      (ρ u) j ≤ N * ∑ v, R.queryWeight I
        (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ i p else 0)) (x v) (ρ v) j := by
    rw [h1, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ ↦ hv v
  exact (ENNReal.mul_le_mul_iff_right hN0 hNtop).mp h2

open scoped Classical in
/-- **The adaptive view lemma with a count per input state**, summed over the calls: if at every
input state `p` the families agreeing on its label with `p ∈ C u i` are at most `κ i p` times all
of them, the masses of `C v` add up over the hidden values to at most the `κ`-weighted
diagonals. -/
theorem sum_totalWeight_le_cnt [∀ s, Nonempty (D s)] (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ v, (ρ v).PosSemidef)
    (P : spec.Port → Prop) (hview : ∀ j, ViewByOn R I P lab x ρ j)
    (C : ((s : S) → D s) → ∀ i, Set (spec.In i × R.D)) (hCP : ∀ v i, ¬ P i → C v i = ∅)
    (κ : ∀ i, spec.In i × R.D → ℝ≥0∞)
    (hcnt : ∀ v i p, ∑ u, (if Agree (lab p.2) v u ∧ p ∈ C u i then (1 : ℝ≥0∞) else 0) ≤
      κ i p * ∑ u, if Agree (lab p.2) v u then 1 else 0) :
    ∑ v, R.totalWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) ≤
      ∑ v, R.totalWeight I (fun i ↦ kWt (κ i)) (x v) (ρ v) := by
  have h := sum_totalWeight_le_of_forall R I (fun v i ↦ diagMass (C v i)) (fun i ↦ kWt (κ i)) x
    ρ 1 fun j ↦ by
      rw [one_mul]
      have hpart : ∀ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j =
          ∑ T, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v) (ρ v) j :=
        fun v ↦ by
          rw [← queryWeight_fintype_sum]
          refine congrArg (fun w ↦ R.queryWeight I w (x v) (ρ v) j)
            (funext fun i ↦ funext fun σ ↦ ?_)
          exact diagMass_eq_sum_label (fun p ↦ lab p.2) (C v i) σ
      have hκpart : ∀ v, R.queryWeight I (fun i ↦ kWt (κ i)) (x v) (ρ v) j =
          ∑ T, R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ i p else 0))
            (x v) (ρ v) j :=
        fun v ↦ by
          rw [← queryWeight_fintype_sum]
          refine congrArg (fun w ↦ R.queryWeight I w (x v) (ρ v) j)
            (funext fun i ↦ funext fun σ ↦ ?_)
          simp only [kWt]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      calc ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j
          = ∑ T, ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v)
              (ρ v) j := by
            simp only [hpart]
            exact Finset.sum_comm
        _ ≤ ∑ T, ∑ v, R.queryWeight I
              (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ i p else 0)) (x v) (ρ v) j :=
            Finset.sum_le_sum fun T _ ↦ sum_queryWeight_cut_le_cnt R I lab x ρ hρ j P
              (hview j) C hCP κ hcnt T
        _ = _ := by
            rw [Finset.sum_comm]
            simp only [hκpart]
  rwa [one_mul] at h

end view

end Quantum.Sphincs.Assembly

end
