module

public import Quantum.Xmss.Hybrid.View

@[expose] public section

/-!
# Hidden masses under adaptive disclosures

The view lemma of the hidden-cell hybrid (design, sections 5.3 and 8) for the chain, leaf and node
cells, whose hidden set shrinks as signatures disclose values, and for the `k'` and `h` cells of
hidden paths.

**Lazy sampling.** The table is reparametrized into public data and hidden values
`v : (s : S) → D s`, independent and uniform. The register carries a classical label
`lab : R.D → Finset S`, the coordinates disclosed so far. The lazy-sampling property of the game is
`ViewByOn` (for the weights vanishing outside a set `P` of ports): the part of the input of the
`j`-th call on the register states labelled `T` (every diagonal mass of a set of such states)
depends on the hidden values only through their coordinates in `T`. Disclosure is adaptive: which
coordinates are in `T` depends on the run. `ViewBy` asks it of every weight (`ViewBy.viewByOn`); for
runtime 2 the hidden masses vanish on the program ports, so `ViewByOn` for the other ports suffices.

* `sum_queryWeight_view_le` (**the adaptive view lemma**): if every input state `p` in the set
  `C v i` names coordinates `srcs i p`, one of which is undisclosed (`∉ lab p.2`) and has its hidden
  value in a set `F i p s v` that does not depend on that coordinate, then the masses of `C v` add up
  over `v` to at most `κ` times the traces, where `κ` bounds `∑ₛ |F i p s v| / |D s|`.
  `avg_le_of_sum_le` turns such sums into averages over the table.
* `sum_queryWeight_hiddenMass_le`: the same for the hidden mass of runtime 2, with sources given
  cell by cell (`h`, `k`, `k'` cells, read ports included); program ports carry no mass.
* `sum_queryWeight_hiddenK_digest_le`: hidden `k`-cells each naming one undisclosed 128-bit value
  it carries: `2^-128` per call.
* `sum_queryWeight_hiddenK'_le`, `sum_queryWeight_hiddenH_le` (the `k'` and `h` cells of hidden
  paths): a `k'`-cell `(π (y, c + a)).1` with a hidden `k`-value `a`: at most `|S| G / |Z|` per call
  for a `PermGood π G` permutation; an `h`-cell `w + a'` with a hidden `k'`-value `a'`: at most
  `|S| / |Z|` per call. `sum_queryWeight_hiddenKNext_le`: the `k`-cell `u + a` of a later block,
  with `a` the hidden `h`-value of the previous round: at most `|S| / |X|` per call.
* leanXMSS's cells: `payloadLo`, `payloadHi` (bits `256` to `383` and `384` to `511` of a first
  block, the payload's first two 16-byte values); `honestCell L s` (the first block of slot `s`'s
  honest input) names its slot (`slotOfBlock_honestCell`) and carries the honest input values:
  the chain value for a chain step, the first chain end for a leaf, both children for a node.
  `ValPos`: the positions of the honest 128-bit values (chain positions, tree values), `valuePos L`.
  `cellSrc P T x`: the position and value a first block names for the disclosed positions `T` (a
  node names its right child when its left one is disclosed); `cellSrc_honestCell_chain`,
  `cellSrc_honestCell_leaf`, `cellSrc_honestCell_node`: on the honest first blocks it names the
  honest value at its position, and a node's named child is disclosed only if both are.

The 128-bit bound covers the first block of each input. A leaf input spans 8 blocks: its first
block carries the first chain ends (`cellSrc_honestCell_leaf` names chain end `0`); its later
`k`-cells are covered by `sum_queryWeight_hiddenKNext_le`, through the hidden `h`-value of the
previous round, at `|S| / |X|` per call.
-/

open Matrix
open scoped ENNReal ComplexOrder

universe u v w u₁ v₁

namespace Quantum.Xmss.Hybrid

open Quantum QuantumRuntime

/-! ## Hidden values agreeing on disclosed coordinates -/

section coords

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)]

/-- Two families of hidden values agree on the coordinates `T`. -/
def Agree (T : Finset S) (v v' : (s : S) → D s) : Prop :=
  ∀ s ∈ T, v s = v' s

instance (T : Finset S) (v v' : (s : S) → D s) : Decidable (Agree T v v') := by
  unfold Agree
  infer_instance

omit [Fintype S] [DecidableEq S] [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem Agree.symm {T : Finset S} {v v' : (s : S) → D s} (h : Agree T v v') : Agree T v' v :=
  fun s hs ↦ (h s hs).symm

omit [Fintype S] [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem agree_update_iff {T : Finset S} {s : S} (hs : s ∉ T) (v u : (s : S) → D s) (d : D s) :
    Agree T v (Function.update u s d) ↔ Agree T v u := by
  unfold Agree
  refine forall₂_congr fun s' hs' ↦ ?_
  have hne : s' ≠ s := by
    rintro rfl
    exact hs hs'
  rw [Function.update_of_ne hne]

omit [∀ s, DecidableEq (D s)] in
/-- Changing one coordinate in every possible way covers every family `|D s|` times. -/
theorem sum_sum_update (s : S) (g : ((s : S) → D s) → ℝ≥0∞) :
    ∑ u, ∑ d : D s, g (Function.update u s d) = Fintype.card (D s) * ∑ u, g u := by
  have hu : ∀ (a : D s) (r : ∀ j : {j // j ≠ s}, D j) (d : D s),
      Function.update ((Equiv.piSplitAt s D).symm (a, r)) s d =
        (Equiv.piSplitAt s D).symm (d, r) := by
    intro a r d
    funext j
    by_cases hj : j = s
    · subst hj
      simp [Equiv.piSplitAt_symm_apply]
    · simp [Equiv.piSplitAt_symm_apply, hj]
  conv_lhs => rw [← (Equiv.piSplitAt s D).symm.sum_comp, Fintype.sum_prod_type]
  conv_rhs => rw [← (Equiv.piSplitAt s D).symm.sum_comp, Fintype.sum_prod_type]
  simp only [hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_comm]

/-- **Counting along one undisclosed coordinate.** For `s ∉ T` and sets `F u` that do not depend on
`u s`, the families agreeing with `v` on `T` whose coordinate `s` lies in `F u` are a `|D s|`-th of
the weighted count `∑ |F u|`. -/
theorem card_mul_sum_agree_mem (T : Finset S) (v : (s : S) → D s) {s : S} (hs : s ∉ T)
    (F : ((s : S) → D s) → Finset (D s)) (hF : ∀ u d, F (Function.update u s d) = F u) :
    (Fintype.card (D s) : ℝ≥0∞) * ∑ u, (if Agree T v u ∧ u s ∈ F u then 1 else 0) =
      ∑ u, if Agree T v u then ((F u).card : ℝ≥0∞) else 0 := by
  rw [← sum_sum_update s]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  simp only [agree_update_iff hs, Function.update_self, hF]
  by_cases h : Agree T v u
  · simp [h]
  · simp [h]

/-- The number of families agreeing with `v` on `T` does not depend on `v`. -/
theorem sum_agree_eq (T : Finset S) (v v₀ : (s : S) → D s) :
    ∑ u, (if Agree T v u then (1 : ℝ≥0∞) else 0) = ∑ u, if Agree T v₀ u then 1 else 0 := by
  let e : ((s : S) → D s) ≃ ((s : S) → D s) := Equiv.piCongrRight fun s ↦
    if s ∈ T then Equiv.swap (v s) (v₀ s) else Equiv.refl _
  refine Fintype.sum_equiv e _ _ fun u ↦ ?_
  have h : Agree T v u ↔ Agree T v₀ (e u) := by
    unfold Agree
    refine forall₂_congr fun s hs ↦ ?_
    have he : e u s = Equiv.swap (v s) (v₀ s) (u s) := by
      simp [e, hs]
    rw [he, eq_comm (a := v₀ s), Equiv.swap_apply_eq_iff, Equiv.swap_apply_right, eq_comm]
  simp only [h]

/-- **The count of a family of sources.** If every family `u` with `P u` has an undisclosed source
`s ∈ srcs`, `s ∉ T`, whose value lies in `F s u` (which does not depend on `u s`), the families
agreeing with `v` on `T` with `P` are at most `κ` times all those agreeing with `v` on `T`, where
`κ` bounds `∑ₛ |F s u| / |D s|`. -/
theorem sum_agree_and_le [∀ s, Nonempty (D s)] (T : Finset S) (v : (s : S) → D s)
    (P : ((s : S) → D s) → Prop) [DecidablePred P] (srcs : Finset S)
    (F : (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ s u d, F s (Function.update u s d) = F s u)
    (hP : ∀ u, P u → ∃ s ∈ srcs, s ∉ T ∧ u s ∈ F s u) (κ : ℝ≥0∞)
    (hκ : ∀ u, ∑ s ∈ srcs, ((F s u).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) :
    ∑ u, (if Agree T v u ∧ P u then (1 : ℝ≥0∞) else 0) ≤
      κ * ∑ u, if Agree T v u then 1 else 0 := by
  calc ∑ u, (if Agree T v u ∧ P u then (1 : ℝ≥0∞) else 0)
      ≤ ∑ u, ∑ s ∈ srcs.filter (· ∉ T), (if Agree T v u ∧ u s ∈ F s u then 1 else 0) := by
        refine Finset.sum_le_sum fun u _ ↦ ?_
        split_ifs with h
        · obtain ⟨s, hs, hsT, hsF⟩ := hP u h.2
          refine le_trans ?_ (Finset.single_le_sum
            (f := fun s ↦ if Agree T v u ∧ u s ∈ F s u then (1 : ℝ≥0∞) else 0)
            (fun _ _ ↦ by simp) (Finset.mem_filter.mpr ⟨hs, hsT⟩))
          simp [h.1, hsF]
        · simp
    _ = ∑ s ∈ srcs.filter (· ∉ T), ∑ u, (if Agree T v u ∧ u s ∈ F s u then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ s ∈ srcs.filter (· ∉ T), (Fintype.card (D s) : ℝ≥0∞)⁻¹ *
          ∑ u, (if Agree T v u then ((F s u).card : ℝ≥0∞) else 0) := by
        refine Finset.sum_congr rfl fun s hs ↦ ?_
        rw [← card_mul_sum_agree_mem T v (Finset.mem_filter.mp hs).2 (F s) (hF s), ← mul_assoc,
          ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]
    _ = ∑ u, ∑ s ∈ srcs.filter (· ∉ T), (Fintype.card (D s) : ℝ≥0∞)⁻¹ *
          (if Agree T v u then ((F s u).card : ℝ≥0∞) else 0) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ u, if Agree T v u then ∑ s ∈ srcs.filter (· ∉ T),
          ((F s u).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ else 0 := by
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        by_cases h : Agree T v u
        · simp only [h, ↓reduceIte]
          exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
        · simp [h]
    _ ≤ ∑ u, if Agree T v u then κ else 0 := by
        refine Finset.sum_le_sum fun u _ ↦ ?_
        split_ifs
        · exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans (hκ u)
        · exact le_rfl
    _ = κ * ∑ u, if Agree T v u then 1 else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        split_ifs <;> simp

end coords

/-! ## The adaptive view lemma -/

section view

/-- A diagonal mass splits along a labelling of the basis states. -/
theorem diagMass_eq_sum_label {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (lab : α → β) (C : Set α) (σ : Matrix α α ℂ) :
    diagMass C σ = ∑ b, diagMass (C ∩ {a | lab a = b}) σ := by
  simp only [diagMass]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_eq_single (lab a) (fun b _ hb ↦ Set.indicator_of_notMem
    (fun h ↦ hb h.2.symm) _) (by simp)]
  by_cases ha : a ∈ C
  · rw [Set.indicator_of_mem ha,
      Set.indicator_of_mem (show a ∈ C ∩ {a' | lab a' = lab a} from ⟨ha, rfl⟩)]
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem fun h ↦ ha h.1]

/-- **The pointwise count.** On a finite set of labelled basis states, if every state `a ∈ C u` has
an undisclosed source with its value in `F a s u`, the masses of the states of `C u` labelled `T`,
over the families `u` agreeing with `v` on `T`, add up to at most `κ` times their number times the
mass of all states labelled `T`. -/
theorem sum_agree_diagMass_le {S : Type} [Fintype S] [DecidableEq S] {D : S → Type}
    [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] [∀ s, Nonempty (D s)] {α : Type} [Fintype α]
    (lab : α → Finset S) (T : Finset S) (v : (s : S) → D s) (C : ((s : S) → D s) → Set α)
    (srcs : α → Finset S) (F : α → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ a s u d, F a s (Function.update u s d) = F a s u)
    (hsrc : ∀ u a, a ∈ C u → ∃ s ∈ srcs a, s ∉ lab a ∧ u s ∈ F a s u) (κ : ℝ≥0∞)
    (hκ : ∀ a u, ∑ s ∈ srcs a,
      ((F a s u).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) (σ : Matrix α α ℂ) :
    ∑ u, (if Agree T v u then diagMass (C u ∩ {a | lab a = T}) σ else 0) ≤
      κ * (∑ u, if Agree T v u then (1 : ℝ≥0∞) else 0) * diagMass {a | lab a = T} σ := by
  classical
  simp only [diagMass]
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
        · rw [Set.indicator_of_mem (show a ∈ {a | lab a = T} from ha)]
          calc ∑ u, (if Agree T v u then
                  (C u ∩ {a | lab a = T}).indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a else 0)
              = ENNReal.ofReal (σ a a).re *
                  ∑ u, (if Agree T v u ∧ a ∈ C u then (1 : ℝ≥0∞) else 0) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun u _ ↦ ?_
                by_cases h1 : Agree T v u <;> by_cases h2 : a ∈ C u <;>
                  simp [h1, h2, ha]
            _ ≤ ENNReal.ofReal (σ a a).re *
                  (κ * ∑ u, if Agree T v u then (1 : ℝ≥0∞) else 0) := by
                gcongr
                exact sum_agree_and_le T v (fun u ↦ a ∈ C u) (srcs a) (F a) (hF a)
                  (fun u hu ↦ by
                    obtain ⟨s, hs, hsl, hsF⟩ := hsrc u a hu
                    exact ⟨s, hs, ha ▸ hsl, hsF⟩) κ (hκ a)
            _ = _ := by ring
        · rw [Set.indicator_of_notMem (show a ∉ {a | lab a = T} from ha), mul_zero]
          refine le_of_eq (Finset.sum_eq_zero fun u _ ↦ ?_)
          split_ifs
          · exact Set.indicator_of_notMem (fun h ↦ ha h.2) _
          · rfl

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)]
  {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- Weights of a finite sum of weights. -/
theorem queryWeight_fintype_sum {κ : Type*} [Fintype κ]
    (w : κ → ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec Ω A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    R.queryWeight I (fun i σ ↦ ∑ c, w c i σ) x ρ j = ∑ c, R.queryWeight I (w c) x ρ j := by
  have h := R.tsum_queryWeight I w x ρ j
  simp only [tsum_fintype] at h
  exact h.symm

/-- The zero weight. -/
theorem queryWeight_zero_weight (x : QuantumComp L spec Ω A) (ρ : Matrix (A × R.D) (A × R.D) ℂ)
    (j : ℕ) : R.queryWeight I (fun _ _ ↦ 0) x ρ j = 0 := by
  have h := R.queryWeight_const_mul I 0 (w := fun _ _ ↦ 0) x ρ j
  simpa using h

/-- **The lazy-sampling property.** The input of the `j`-th call of the run of `x v` from `ρ v`,
restricted to the register states labelled `T`, depends on the hidden values `v` only through
their coordinates in `T`: the diagonal masses of sets of states labelled `T` agree for families
that agree on `T`. -/
def ViewBy (lab : R.D → Finset S) (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) : Prop :=
  ∀ (T : Finset S) (v v' : (s : S) → D s), Agree T v v' →
    ∀ C : ∀ i, Set (spec.In i × R.D), (∀ i p, p ∈ C i → lab p.2 = T) →
      R.queryWeight I (fun i ↦ diagMass (C i)) (x v) (ρ v) j =
        R.queryWeight I (fun i ↦ diagMass (C i)) (x v') (ρ v') j

/-- **The lazy-sampling property on some ports**: `ViewBy` for the weights that vanish on the ports
outside `P`. -/
def ViewByOn (P : spec.Port → Prop) (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) : Prop :=
  ∀ (T : Finset S) (v v' : (s : S) → D s), Agree T v v' →
    ∀ C : ∀ i, Set (spec.In i × R.D), (∀ i p, p ∈ C i → lab p.2 = T) → (∀ i, ¬ P i → C i = ∅) →
      R.queryWeight I (fun i ↦ diagMass (C i)) (x v) (ρ v) j =
        R.queryWeight I (fun i ↦ diagMass (C i)) (x v') (ρ v') j

omit [Fintype S] [DecidableEq S] [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
variable {R I} in
/-- The lazy-sampling property gives it on every set of ports. -/
theorem ViewBy.viewByOn {lab : R.D → Finset S} {x : ((s : S) → D s) → QuantumComp L spec Ω A}
    {ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ} {j : ℕ} (h : ViewBy R I lab x ρ j)
    (P : spec.Port → Prop) : ViewByOn R I P lab x ρ j :=
  fun T v v' hv C hC _ ↦ h T v v' hv C hC

/-- **The view lemma at one label.** The masses at the states labelled `T` of the sets `C v`, summed
over the hidden values, are at most `κ` times the masses of all states labelled `T`. -/
theorem sum_queryWeight_cut_le [∀ s, Nonempty (D s)] (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (P : spec.Port → Prop) (hview : ViewByOn R I P lab x ρ j)
    (C : ((s : S) → D s) → ∀ i, Set (spec.In i × R.D)) (hCP : ∀ v i, ¬ P i → C v i = ∅)
    (srcs : ∀ i, spec.In i × R.D → Finset S)
    (F : ∀ i, spec.In i × R.D → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ i p s v d, F i p s (Function.update v s d) = F i p s v)
    (hsrc : ∀ v i p, p ∈ C v i → ∃ s ∈ srcs i p, s ∉ lab p.2 ∧ v s ∈ F i p s v)
    (κ : ℝ≥0∞)
    (hκ : ∀ i p v, ∑ s ∈ srcs i p,
      ((F i p s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) (T : Finset S) :
    ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v) (ρ v) j ≤
      κ * ∑ v, R.queryWeight I (fun i ↦ diagMass {p : spec.In i × R.D | lab p.2 = T})
        (x v) (ρ v) j := by
  classical
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
        κ * N * R.queryWeight I (fun i ↦ diagMass {p : spec.In i × R.D | lab p.2 = T})
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
    have h := sum_agree_diagMass_le (fun p : spec.In i × R.D ↦ lab p.2) T v (fun u ↦ C u i)
      (srcs i) (F i) (hF i) (fun u p hp ↦ hsrc u i p hp) κ (fun p u ↦ hκ i p u) σ
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
      (ρ u) j ≤ N * (κ * ∑ v, R.queryWeight I
        (fun i ↦ diagMass {p : spec.In i × R.D | lab p.2 = T}) (x v) (ρ v) j) := by
    rw [h1, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ ↦ (hv v).trans_eq (by ring)
  exact (ENNReal.mul_le_mul_iff_right hN0 hNtop).mp h2

/-- **The adaptive view lemma.** Under the lazy-sampling property, let every input state `p ∈ C v i`
of a call have a source `s ∈ srcs i p` that is not disclosed in `p` and whose hidden value lies in
`F i p s v`, a set that does not depend on `v s`. Then the masses of `C v` at the `j`-th call add up,
over the hidden values, to at most `κ` times the traces, where `κ` bounds `∑ₛ |F i p s v| / |D s|`.
With `|V|` families of hidden values and initial states of trace at most `1`, the average mass is at
most `κ`. -/
theorem sum_queryWeight_view_le [∀ s, Nonempty (D s)] (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (P : spec.Port → Prop) (hview : ViewByOn R I P lab x ρ j)
    (C : ((s : S) → D s) → ∀ i, Set (spec.In i × R.D)) (hCP : ∀ v i, ¬ P i → C v i = ∅)
    (srcs : ∀ i, spec.In i × R.D → Finset S)
    (F : ∀ i, spec.In i × R.D → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ i p s v d, F i p s (Function.update v s d) = F i p s v)
    (hsrc : ∀ v i p, p ∈ C v i → ∃ s ∈ srcs i p, s ∉ lab p.2 ∧ v s ∈ F i p s v)
    (κ : ℝ≥0∞)
    (hκ : ∀ i p v, ∑ s ∈ srcs i p,
      ((F i p s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) :
    ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j ≤
      κ * ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  classical
  have hpart : ∀ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j =
      ∑ T, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v) (ρ v) j :=
    fun v ↦ by
      rw [← queryWeight_fintype_sum]
      refine congrArg (fun w ↦ R.queryWeight I w (x v) (ρ v) j) (funext fun i ↦ funext fun σ ↦ ?_)
      exact diagMass_eq_sum_label (fun p ↦ lab p.2) (C v i) σ
  have hT : ∀ T, ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v)
      (ρ v) j ≤ κ * ∑ v, R.queryWeight I (fun i ↦ diagMass {p : spec.In i × R.D | lab p.2 = T})
        (x v) (ρ v) j :=
    fun T ↦ sum_queryWeight_cut_le R I lab x ρ hρ j P hview C hCP srcs F hF hsrc κ hκ T
  have htr : ∀ v, ∑ T, R.queryWeight I (fun i ↦ diagMass {p : spec.In i × R.D | lab p.2 = T})
      (x v) (ρ v) j ≤ ENNReal.ofReal (ρ v).trace.re := fun v ↦ by
    rw [← queryWeight_fintype_sum]
    refine R.queryWeight_le_ofReal_trace I (fun i σ hσ ↦ ?_) (x v) (hρ v) j
    have h := diagMass_eq_sum_label (fun p : spec.In i × R.D ↦ lab p.2) Set.univ σ
    simp only [Set.univ_inter] at h
    rw [← h]
    exact diagMass_le _ hσ
  calc ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j
      = ∑ T, ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v)
          (ρ v) j := by
        simp only [hpart]
        exact Finset.sum_comm
    _ ≤ ∑ T, κ * ∑ v, R.queryWeight I (fun i ↦ diagMass {p : spec.In i × R.D | lab p.2 = T})
          (x v) (ρ v) j :=
        Finset.sum_le_sum fun T _ ↦ hT T
    _ = κ * ∑ v, ∑ T, R.queryWeight I (fun i ↦ diagMass {p : spec.In i × R.D | lab p.2 = T})
          (x v) (ρ v) j := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ κ * ∑ v, ENNReal.ofReal (ρ v).trace.re := by
        gcongr with v
        exact htr v

/-- **From sums over the hidden values to the average over the tables.** If the uniformly drawn
table is `e : Θ ≃ P × V` (public data and hidden values) and, for every public part, the sum over
the hidden values is at most `κ |V|`, the average over the tables is at most `κ`. -/
theorem avg_le_of_sum_le {Θ P V : Type*} [Fintype Θ] [Fintype P] [Fintype V] (e : Θ ≃ P × V)
    (f : Θ → ℝ≥0∞) (κ : ℝ≥0∞) (h : ∀ p, ∑ v, f (e.symm (p, v)) ≤ κ * Fintype.card V) :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ θ, f θ ≤ κ := by
  rw [← e.symm.sum_comp, Fintype.sum_prod_type, Fintype.card_congr e, Fintype.card_prod,
    Nat.cast_mul]
  by_cases h0 : ((Fintype.card P : ℝ≥0∞) * Fintype.card V) = 0
  · rcases mul_eq_zero.mp h0 with hP | hV
    · have : IsEmpty P := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hP)
      simp
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hV)
      simp
  · calc ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * ∑ p, ∑ v, f (e.symm (p, v))
        ≤ ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * ∑ _p : P, κ * Fintype.card V := by
          gcongr with p
          exact h p
      _ = κ * (((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ *
            ((Fintype.card P : ℝ≥0∞) * Fintype.card V)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ = κ := by
          rw [ENNReal.inv_mul_cancel h0 (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
            (ENNReal.natCast_ne_top _)), mul_one]

end view

/-! ## The hidden masses of runtime 2 -/

section hw

open Quantum.Sponge

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

/-- The sets of input states whose diagonal masses are the hidden masses (`hiddenMass`). -/
def hidSet (Hh : Set Z) (Hk Hk' : Set X) :
    ∀ i : (hwSpec X Z M).Port, Set ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
  | .inl (.inl .h) => {p : (Z × X) × HwReg X Z M | p.1.1 ∈ Hh ∧ p.2.2.1.1 p.1.1 = none}
  | .inl (.inl .k) => {p : (X × Z) × HwReg X Z M | p.1.1 ∈ Hk ∧ p.2.2.1.2.1 p.1.1 = none}
  | .inl (.inl .k') => {p : (X × Z) × HwReg X Z M | p.1.1 ∈ Hk' ∧ p.2.2.1.2.2 p.1.1 = none}
  | .inl (.inr (.readH z _)) => {p : Unit × HwReg X Z M | z ∈ Hh ∧ p.2.2.1.1 z = none}
  | .inl (.inr (.readK x _)) => {p : Unit × HwReg X Z M | x ∈ Hk ∧ p.2.2.1.2.1 x = none}
  | .inl (.inr (.readK' x _)) => {p : Unit × HwReg X Z M | x ∈ Hk' ∧ p.2.2.1.2.2 x = none}
  | .inr _ => ∅

theorem hiddenMass_eq_diagMass (Hh : Set Z) (Hk Hk' : Set X) :
    hiddenMass (M := M) Hh Hk Hk' = fun i ↦ diagMass (hidSet Hh Hk Hk' i) := by
  funext i σ
  rcases i with ((_ | _ | _) | (⟨z, upd⟩ | ⟨x, upd⟩ | ⟨x, upd⟩)) | c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (Finset.sum_eq_zero fun a _ ↦ Set.indicator_of_notMem (Set.notMem_empty a) _).symm

/-- Cell-level data lifted to the ports: a sponge port's input names its query cell, a read port
its read cell; the program ports take `b`. -/
def liftCells {β : Type*} (gh : Z → HwReg X Z M → β) (gk gk' : X → HwReg X Z M → β) (b : β) :
    ∀ i : (hwSpec X Z M).Port, (hwSpec X Z M).In i × QReg.of (HwReg X Z M) → β
  | .inl (.inl .h) => fun p ↦ gh p.1.1 p.2
  | .inl (.inl .k) => fun p ↦ gk p.1.1 p.2
  | .inl (.inl .k') => fun p ↦ gk' p.1.1 p.2
  | .inl (.inr (.readH z _)) => fun p ↦ gh z p.2
  | .inl (.inr (.readK x _)) => fun p ↦ gk x p.2
  | .inl (.inr (.readK' x _)) => fun p ↦ gk' x p.2
  | .inr _ => fun _ ↦ b

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {L : LocalSig.{u, v}} (I : L.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **The adaptive view lemma for the hidden mass of runtime 2.** The sources are given cell by
cell: every hidden `h`-cell `z ∈ Hh v` that is not hardwired in the register `r` names sources
`sh z r`, one of which is undisclosed in `r` with its hidden value in `Fh z r s v`; likewise the
`k`- and `k'`-cells. Under the lazy-sampling property, the hidden masses of the `j`-th call add up
over the hidden values to at most `κ` times the traces. -/
theorem sum_queryWeight_hiddenMass_le {D : S → Type} [∀ s, Fintype (D s)]
    [∀ s, DecidableEq (D s)] [∀ s, Nonempty (D s)] (m₀ : M) (lab : HwReg X Z M → Finset S)
    (x : ((s : S) → D s) → QuantumComp L (hwSpec X Z M) Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (hview : ViewByOn (runtime2 X Z m₀) I (fun i ↦ i.isLeft = true) lab x ρ j)
    (Hh : ((s : S) → D s) → Set Z) (Hk Hk' : ((s : S) → D s) → Set X)
    (sh : Z → HwReg X Z M → Finset S) (sk sk' : X → HwReg X Z M → Finset S)
    (Fh : Z → HwReg X Z M → (s : S) → ((s : S) → D s) → Finset (D s))
    (Fk Fk' : X → HwReg X Z M → (s : S) → ((s : S) → D s) → Finset (D s))
    (hFh : ∀ z r s v d, Fh z r s (Function.update v s d) = Fh z r s v)
    (hFk : ∀ y r s v d, Fk y r s (Function.update v s d) = Fk y r s v)
    (hFk' : ∀ y r s v d, Fk' y r s (Function.update v s d) = Fk' y r s v)
    (hh : ∀ v z r, z ∈ Hh v → r.2.1.1 z = none → ∃ s ∈ sh z r, s ∉ lab r ∧ v s ∈ Fh z r s v)
    (hk : ∀ v y r, y ∈ Hk v → r.2.1.2.1 y = none →
      ∃ s ∈ sk y r, s ∉ lab r ∧ v s ∈ Fk y r s v)
    (hk' : ∀ v y r, y ∈ Hk' v → r.2.1.2.2 y = none →
      ∃ s ∈ sk' y r, s ∉ lab r ∧ v s ∈ Fk' y r s v)
    (κ : ℝ≥0∞)
    (hκh : ∀ z r v, ∑ s ∈ sh z r,
      ((Fh z r s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ)
    (hκk : ∀ y r v, ∑ s ∈ sk y r,
      ((Fk y r s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ)
    (hκk' : ∀ y r v, ∑ s ∈ sk' y r,
      ((Fk' y r s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) :
    ∑ v, (runtime2 X Z m₀).queryWeight I (hiddenMass (Hh v) (Hk v) (Hk' v)) (x v) (ρ v) j ≤
      κ * ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  simp only [hiddenMass_eq_diagMass]
  refine sum_queryWeight_view_le (runtime2 X Z m₀) I lab x ρ hρ j _ hview
    (fun v ↦ hidSet (Hh v) (Hk v) (Hk' v))
    (fun v i hi ↦ by rcases i with i | c; exacts [absurd rfl hi, rfl]) (liftCells sh sk sk' ∅)
    (liftCells Fh Fk Fk' fun _ _ ↦ ∅) (fun i p s v d ↦ ?_) (fun v i p hp ↦ ?_) κ
    (fun i p v ↦ ?_)
  · rcases i with ((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c
    · exact hFh _ _ s v d
    · exact hFk _ _ s v d
    · exact hFk' _ _ s v d
    · exact hFh _ _ s v d
    · exact hFk _ _ s v d
    · exact hFk' _ _ s v d
    · rfl
  · rcases i with ((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c
    · exact hh v _ _ hp.1 hp.2
    · exact hk v _ _ hp.1 hp.2
    · exact hk' v _ _ hp.1 hp.2
    · exact hh v _ _ hp.1 hp.2
    · exact hk v _ _ hp.1 hp.2
    · exact hk' v _ _ hp.1 hp.2
    · exact hp.elim
  · rcases i with ((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c
    · exact hκh _ _ v
    · exact hκk _ _ v
    · exact hκk' _ _ v
    · exact hκh _ _ v
    · exact hκk _ _ v
    · exact hκk' _ _ v
    · simp [liftCells]

/-- **Hidden `k`-cells naming one 128-bit value.** If every hidden `k`-cell `y ∈ Hk v` that is not
hardwired names a position `src y r`, undisclosed in the register, whose hidden value is the value
`val y r` the cell carries, the hidden mass is `2^-128` per call on average. -/
theorem sum_queryWeight_hiddenK_digest_le (m₀ : M) (lab : HwReg X Z M → Finset S)
    (x : (S → HashSig.Digest) → QuantumComp L (hwSpec X Z M) Ω A)
    (ρ : (S → HashSig.Digest) →
      Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (hview : ViewByOn (D := fun _ : S ↦ HashSig.Digest) (runtime2 X Z m₀) I
      (fun i ↦ i.isLeft = true) lab x ρ j)
    (Hk : (S → HashSig.Digest) → Set X) (src : X → HwReg X Z M → S)
    (val : X → HwReg X Z M → HashSig.Digest)
    (hk : ∀ v y r, y ∈ Hk v → r.2.1.2.1 y = none → src y r ∉ lab r ∧ v (src y r) = val y r) :
    ∑ v, (runtime2 X Z m₀).queryWeight I (hiddenMass ∅ (Hk v) ∅) (x v) (ρ v) j ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  have hcard : (Fintype.card HashSig.Digest : ℝ≥0∞) = 2 ^ 128 := by
    rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
    norm_num [HashSig.digestBits]
  refine sum_queryWeight_hiddenMass_le (D := fun _ : S ↦ HashSig.Digest) I m₀ lab x ρ hρ j hview
    (fun _ ↦ ∅) Hk (fun _ ↦ ∅) (fun _ _ ↦ ∅) (fun y r ↦ {src y r}) (fun _ _ ↦ ∅)
    (fun _ _ _ _ ↦ ∅) (fun y r _ _ ↦ {val y r}) (fun _ _ _ _ ↦ ∅) (fun _ _ _ _ _ ↦ rfl)
    (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ hz ↦ hz.elim) (fun v y r hy hW ↦ ?_)
    (fun _ _ _ hy ↦ hy.elim) _ (fun _ _ _ ↦ by simp) (fun y r v ↦ ?_) (fun _ _ _ ↦ by simp)
  · obtain ⟨h1, h2⟩ := hk v y r hy hW
    exact ⟨src y r, Finset.mem_singleton_self _, h1, by simp [h2]⟩
  · simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul]
    show (Fintype.card HashSig.Digest : ℝ≥0∞)⁻¹ ≤ _
    rw [hcard]

omit [Fintype X] [DecidableEq Z] [AddCommGroup X] [Nonempty X] [Nonempty Z] in
/-- A shifted rate count: the capacities `a` with `(π (y, c + a)).1 = x'` are as many as those
`π` sends from rate `y` to rate `x'`. -/
theorem card_filter_rate_eq (π : Equiv.Perm (X × Z)) (y : X) (c : Z) (x' : X) :
    (Finset.univ.filter fun a : Z ↦ (π (y, c + a)).1 = x').card = rateCount π y x' := by
  rw [rateCount]
  exact Finset.card_equiv (Equiv.addLeft c) fun a ↦ by simp

/-- **The `k'`-cells of hidden paths.** A hidden path `s` reads `k'` at the rate `(π (y, c + a)).1`,
where `a = v s` is its hidden `k`-value and `y`, `c` do not depend on it. If every hidden `k'`-cell
that is not hardwired is such a rate for a path undisclosed in the register, then for a
`PermGood π G` permutation the hidden mass is at most `|S| G / |Z|` per call on average. -/
theorem sum_queryWeight_hiddenK'_le (m₀ : M) (π : Equiv.Perm (X × Z)) {G : ℕ}
    (hπ : PermGood π G) (lab : HwReg X Z M → Finset S)
    (x : (S → Z) → QuantumComp L (hwSpec X Z M) Ω A)
    (ρ : (S → Z) → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (hview : ViewByOn (D := fun _ : S ↦ Z) (runtime2 X Z m₀) I (fun i ↦ i.isLeft = true) lab x
      ρ j)
    (Hk' : (S → Z) → Set X) (y : S → (S → Z) → X) (c : S → (S → Z) → Z)
    (hy : ∀ s v d, y s (Function.update v s d) = y s v)
    (hc : ∀ s v d, c s (Function.update v s d) = c s v)
    (hk' : ∀ v x' r, x' ∈ Hk' v → r.2.1.2.2 x' = none →
      ∃ s, s ∉ lab r ∧ (π (y s v, c s v + v s)).1 = x') :
    ∑ v, (runtime2 X Z m₀).queryWeight I (hiddenMass ∅ ∅ (Hk' v)) (x v) (ρ v) j ≤
      (Fintype.card S * G * (Fintype.card Z : ℝ≥0∞)⁻¹) *
        ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  refine sum_queryWeight_hiddenMass_le (D := fun _ : S ↦ Z) I m₀ lab x ρ hρ j hview
    (fun _ ↦ ∅) (fun _ ↦ ∅) Hk' (fun _ _ ↦ ∅) (fun _ _ ↦ ∅) (fun _ _ ↦ Finset.univ)
    (fun _ _ _ _ ↦ ∅) (fun _ _ _ _ ↦ ∅)
    (fun x' _ s v ↦ Finset.univ.filter fun a : Z ↦ (π (y s v, c s v + a)).1 = x')
    (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl) (fun x' r s v d ↦ by simp only [hy, hc])
    (fun _ _ _ hz ↦ hz.elim) (fun _ _ _ hy ↦ hy.elim) (fun v x' r hx hW ↦ ?_) _
    (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp) (fun x' r v ↦ ?_)
  · obtain ⟨s, hs, he⟩ := hk' v x' r hx hW
    exact ⟨s, Finset.mem_univ _, hs, by simp [he]⟩
  · calc ∑ s ∈ (Finset.univ : Finset S), ((Finset.univ.filter fun a : Z ↦
            (π (y s v, c s v + a)).1 = x').card : ℝ≥0∞) * (Fintype.card Z : ℝ≥0∞)⁻¹
        ≤ ∑ _s ∈ (Finset.univ : Finset S), (G : ℝ≥0∞) * (Fintype.card Z : ℝ≥0∞)⁻¹ := by
          refine Finset.sum_le_sum fun s _ ↦ ?_
          rw [card_filter_rate_eq]
          gcongr
          exact_mod_cast hπ.rate _ _
      _ = Fintype.card S * G * (Fintype.card Z : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- **The `h`-cells of hidden paths.** A hidden path `s` reads `h` at the capacity `w + a'`, where
`a' = v s` is its hidden `k'`-value and `w` does not depend on it. If every hidden `h`-cell that is
not hardwired is such a capacity for a path undisclosed in the register, the hidden mass is at most
`|S| / |Z|` per call on average. -/
theorem sum_queryWeight_hiddenH_le (m₀ : M) (lab : HwReg X Z M → Finset S)
    (x : (S → Z) → QuantumComp L (hwSpec X Z M) Ω A)
    (ρ : (S → Z) → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (hview : ViewByOn (D := fun _ : S ↦ Z) (runtime2 X Z m₀) I (fun i ↦ i.isLeft = true) lab x
      ρ j)
    (Hh : (S → Z) → Set Z) (w : S → (S → Z) → Z)
    (hw : ∀ s v d, w s (Function.update v s d) = w s v)
    (hh : ∀ v z r, z ∈ Hh v → r.2.1.1 z = none → ∃ s, s ∉ lab r ∧ w s v + v s = z) :
    ∑ v, (runtime2 X Z m₀).queryWeight I (hiddenMass (Hh v) ∅ ∅) (x v) (ρ v) j ≤
      (Fintype.card S * (Fintype.card Z : ℝ≥0∞)⁻¹) * ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  refine sum_queryWeight_hiddenMass_le (D := fun _ : S ↦ Z) I m₀ lab x ρ hρ j hview
    Hh (fun _ ↦ ∅) (fun _ ↦ ∅) (fun _ _ ↦ Finset.univ) (fun _ _ ↦ ∅) (fun _ _ ↦ ∅)
    (fun z _ s v ↦ {z - w s v}) (fun _ _ _ _ ↦ ∅) (fun _ _ _ _ ↦ ∅)
    (fun z r s v d ↦ by simp only [hw]) (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl)
    (fun v z r hz hW ↦ ?_) (fun _ _ _ hy ↦ hy.elim) (fun _ _ _ hy ↦ hy.elim) _
    (fun z r v ↦ ?_) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
  · obtain ⟨s, hs, he⟩ := hh v z r hz hW
    exact ⟨s, Finset.mem_univ _, hs, by simp [← he]⟩
  · simp [Finset.card_univ]

/-- **The `k`-cells of later blocks of hidden paths.** A hidden path `s` reads `k` at its next
block `u + a`, where `a = v s` is the `h`-value of its previous round (added to the rate) and `u`
does not depend on it. If every hidden `k`-cell that is not hardwired is such a block for a path
undisclosed in the register, the hidden mass is at most `|S| / |X|` per call on average. This
covers the `k`-cells of the second to last blocks of a multi-block input (the leaf). -/
theorem sum_queryWeight_hiddenKNext_le (m₀ : M) (lab : HwReg X Z M → Finset S)
    (x : (S → X) → QuantumComp L (hwSpec X Z M) Ω A)
    (ρ : (S → X) → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (hview : ViewByOn (D := fun _ : S ↦ X) (runtime2 X Z m₀) I (fun i ↦ i.isLeft = true) lab x
      ρ j)
    (Hk : (S → X) → Set X) (u : S → (S → X) → X)
    (hu : ∀ s v d, u s (Function.update v s d) = u s v)
    (hk : ∀ v y r, y ∈ Hk v → r.2.1.2.1 y = none → ∃ s, s ∉ lab r ∧ u s v + v s = y) :
    ∑ v, (runtime2 X Z m₀).queryWeight I (hiddenMass ∅ (Hk v) ∅) (x v) (ρ v) j ≤
      (Fintype.card S * (Fintype.card X : ℝ≥0∞)⁻¹) * ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  refine sum_queryWeight_hiddenMass_le (D := fun _ : S ↦ X) I m₀ lab x ρ hρ j hview
    (fun _ ↦ ∅) Hk (fun _ ↦ ∅) (fun _ _ ↦ ∅) (fun _ _ ↦ Finset.univ) (fun _ _ ↦ ∅)
    (fun _ _ _ _ ↦ ∅) (fun y _ s v ↦ {y - u s v}) (fun _ _ _ _ ↦ ∅)
    (fun _ _ _ _ _ ↦ rfl) (fun y r s v d ↦ by simp only [hu]) (fun _ _ _ _ _ ↦ rfl)
    (fun _ _ _ hz ↦ hz.elim) (fun v y r hy hW ↦ ?_) (fun _ _ _ hy ↦ hy.elim) _
    (fun _ _ _ ↦ by simp) (fun y r v ↦ ?_) (fun _ _ _ ↦ by simp)
  · obtain ⟨s, hs, he⟩ := hk v y r hy hW
    exact ⟨s, Finset.mem_univ _, hs, by simp [← he]⟩
  · simp [Finset.card_univ]

end hw

/-! ## leanXMSS's first blocks -/

section xmss

open HashSig LeanXmss Quantum.Sponge

/-- Bits `256` to `383` of a rate: in the first block of a tweakable-hash input, its payload's first
16 bytes. -/
def payloadLo (x : X) : Digest :=
  rateSlice x 256 128 (by norm_num)

/-- Bits `384` to `511` of a rate: in the first block of a tweakable-hash input, its payload's
second 16 bytes. -/
def payloadHi (x : X) : Digest :=
  rateSlice x 384 128 (by norm_num)

theorem payloadLo_thInput (Q : PublicParameter) (fields : TweakFields) (a : BitVec (8 * 16))
    (rest : HashInput) :
    payloadLo (blockOf (firstBlock (thInput Q fields (littleEndianBytes 16 a ++ rest)))) = a := by
  have hlen : 48 ≤ (thInput Q fields (littleEndianBytes 16 a ++ rest)).length := by
    rw [length_thInput, List.length_append, length_littleEndianBytes]
    omega
  refine rateSlice_eq fun j hj ↦ ?_
  rw [blockOf_firstBlock _ _ (by change 256 + j < _; omega), Fin.val_mk,
    inputBit_thInput_payload,
    inputBit_append_left _ _ _ (by rw [length_littleEndianBytes]; omega),
    inputBit_littleEndianBytes]

theorem payloadHi_thInput (Q : PublicParameter) (fields : TweakFields) (a b : BitVec (8 * 16))
    (rest : HashInput) :
    payloadHi (blockOf (firstBlock (thInput Q fields
      (littleEndianBytes 16 a ++ littleEndianBytes 16 b ++ rest)))) = b := by
  have hlen : 64 ≤ (thInput Q fields
      (littleEndianBytes 16 a ++ littleEndianBytes 16 b ++ rest)).length := by
    rw [length_thInput, List.length_append, List.length_append, length_littleEndianBytes,
      length_littleEndianBytes]
    omega
  refine rateSlice_eq fun j hj ↦ ?_
  rw [blockOf_firstBlock _ _ (by change 384 + j < _; omega), Fin.val_mk,
    show 384 + j = 256 + (8 * (littleEndianBytes 16 a).length + j) by
      rw [length_littleEndianBytes]; omega,
    inputBit_thInput_payload, List.append_assoc, inputBit_append_right,
    inputBit_append_left _ _ _ (by rw [length_littleEndianBytes]; omega)]
  exact inputBit_littleEndianBytes 16 b j

theorem digestsPayload_succ {n : ℕ} (f : Fin (n + 1) → Digest) :
    digestsPayload f = littleEndianBytes 16 (f 0) ++ digestsPayload fun i : Fin n ↦ f i.succ := by
  rw [digestsPayload, List.ofFn_succ]
  rfl

/-- A position of an honest 128-bit value: position `j` of chain `i` of key `e` of layer `l`, or the
tree value of layer `l` at `level`, index `index` (level `0`: the leaves). -/
inductive ValPos where
  /-- Position `j` of chain `i` of key `e` of layer `l`. -/
  | chain (l : Layer) (e : KeyIndex) (i : ChainIndex) (j : Fin chainLength)
  /-- The tree value of layer `l` at `level`, index `index`. -/
  | tree (l : Layer) (level : Fin (layerHeight + 1)) (index : Fin (2 ^ 32))
  deriving DecidableEq, Fintype

theorem chainStep_lt (step : ChainStep) : step.val < chainLength := by
  have := step.isLt
  omega

theorem chainLength_pred_lt : chainLength - 1 < chainLength :=
  Nat.sub_one_lt (by simp [chainLength])

/-- The position and value a first block names, for the disclosed positions `T`: a chain step's
input value, a leaf's first chain end, a node's left child, or its right child when the left one is
disclosed; the value is read from the block's payload bits. -/
def cellSrc (P : PublicParameter) (T : Finset ValPos) (x : X) : Option (ValPos × Digest) :=
  match slotOfBlock P x with
  | some (.chain l e step i) => some (.chain l e i ⟨step.val, chainStep_lt step⟩, payloadLo x)
  | some (.leaf l e) => some (.chain l e ⟨0, by decide⟩ ⟨chainLength - 1, chainLength_pred_lt⟩,
      payloadLo x)
  | some (.node l level index) =>
      if h : level - 1 < layerHeight + 1 ∧ 2 * index + 1 < 2 ^ 32 then
        if ValPos.tree l ⟨level - 1, h.1⟩ ⟨2 * index, by omega⟩ ∈ T then
          some (.tree l ⟨level - 1, h.1⟩ ⟨2 * index + 1, h.2⟩, payloadHi x)
        else some (.tree l ⟨level - 1, h.1⟩ ⟨2 * index, by omega⟩, payloadLo x)
      else none
  | _ => none

variable (L : HonestTable)

/-- The honest value at a position. -/
def valuePos : ValPos → Digest
  | .chain l e i j => L.chainValue l e i j.val
  | .tree l level index => L.treeValue l level.val index.val

/-- The first block of a slot's honest input. -/
def honestCell (s : Slot) : X :=
  blockOf (firstBlock (thInput L.param (slotFields s) (L.payload s)))

/-- **The first block of an honest input names its slot.** -/
theorem slotOfBlock_honestCell {s : Slot} (hs : InTable s) :
    slotOfBlock L.param (honestCell L s) = some s := by
  have h := L.slotOf_honestTail (s := s)
    (tail := absorbTail L.view (blocks (thInput L.param (slotFields s) (L.payload s))))
    (by simp [HonestTable.honestTail, HonestTable.honestInput, hs])
  obtain ⟨rest, ht, -⟩ := absorbTail_blocks L.view (thInput L.param (slotFields s) (L.payload s))
  rw [ht, slotOf] at h
  split_ifs at h
  · obtain rfl := Option.some.inj h
    exact False.elim hs
  · exact h

theorem payloadLo_honestCell_chain (l : Layer) (e : KeyIndex) (step : ChainStep)
    (i : ChainIndex) :
    payloadLo (honestCell L (.chain l e step i)) = L.chainValue l e i step.val :=
  payloadLo_thInput _ _ _ _

theorem payloadLo_honestCell_leaf (l : Layer) (e : KeyIndex) :
    payloadLo (honestCell L (.leaf l e)) = L.chainValue l e ⟨0, by decide⟩ (chainLength - 1) := by
  show payloadLo (blockOf (firstBlock (thInput L.param _ (digestsPayload (L.endpoints l e))))) = _
  rw [show digestsPayload (L.endpoints l e) = _ from digestsPayload_succ (n := 57) (L.endpoints l e)]
  exact payloadLo_thInput _ _ _ _

theorem payloadLo_honestCell_node (l : Layer) (level index : ℕ) :
    payloadLo (honestCell L (.node l level index)) = L.treeValue l (level - 1) (2 * index) :=
  payloadLo_thInput _ _ _ _

theorem payloadHi_honestCell_node (l : Layer) (level index : ℕ) :
    payloadHi (honestCell L (.node l level index)) =
      L.treeValue l (level - 1) (2 * index + 1) := by
  have h := payloadHi_thInput L.param (slotFields (.node l level index))
    (L.treeValue l (level - 1) (2 * index)) (L.treeValue l (level - 1) (2 * index + 1)) []
  rwa [List.append_nil] at h

/-- **A chain step's first block names its input position and value.** -/
theorem cellSrc_honestCell_chain (T : Finset ValPos) (l : Layer) (e : KeyIndex)
    (step : ChainStep) (i : ChainIndex) (he : e.val < keyCount l) :
    cellSrc L.param T (honestCell L (.chain l e step i)) =
      some (.chain l e i ⟨step.val, chainStep_lt step⟩,
        valuePos L (.chain l e i ⟨step.val, chainStep_lt step⟩)) := by
  rw [cellSrc, slotOfBlock_honestCell L (s := .chain l e step i) he,
    payloadLo_honestCell_chain]
  rfl

/-- **A leaf's first block names its first chain end.** -/
theorem cellSrc_honestCell_leaf (T : Finset ValPos) (l : Layer) (e : KeyIndex)
    (he : e.val < keyCount l) :
    cellSrc L.param T (honestCell L (.leaf l e)) =
      some (.chain l e ⟨0, by decide⟩ ⟨chainLength - 1, chainLength_pred_lt⟩,
        valuePos L (.chain l e ⟨0, by decide⟩ ⟨chainLength - 1, chainLength_pred_lt⟩)) := by
  rw [cellSrc, slotOfBlock_honestCell L (s := .leaf l e) he, payloadLo_honestCell_leaf]
  rfl

/-- **A node's first block names a child**: the left one, or the right one when the left one is
disclosed. Either way the named position carries the honest child value, and it is disclosed only
when both children are. -/
theorem cellSrc_honestCell_node (T : Finset ValPos) (l : Layer) (level index : ℕ)
    (hs : InTable (.node l level index)) :
    ∃ q, cellSrc L.param T (honestCell L (.node l level index)) = some q ∧
      q.2 = valuePos L q.1 ∧
      (q.1 ∈ T → ∀ (h₁ : level - 1 < layerHeight + 1) (h₂ : 2 * index + 1 < 2 ^ 32),
        ValPos.tree l ⟨level - 1, h₁⟩ ⟨2 * index, by omega⟩ ∈ T ∧
          ValPos.tree l ⟨level - 1, h₁⟩ ⟨2 * index + 1, h₂⟩ ∈ T) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hk : 2 ^ (keyBits l - level) ≤ 2 ^ 31 :=
    Nat.pow_le_pow_right (by norm_num) (by have := keyBits_le l; omega)
  have hb : level - 1 < layerHeight + 1 ∧ 2 * index + 1 < 2 ^ 32 := by
    simp only [layerHeight] at h2 ⊢
    omega
  rw [cellSrc, slotOfBlock_honestCell L (s := .node l level index) ⟨h1, h2, h3⟩]
  dsimp only
  simp only [hb.1, hb.2, and_self, ↓reduceDIte]
  split_ifs with hT
  · refine ⟨_, rfl, (payloadHi_honestCell_node L l level index).trans rfl, fun hq _ _ ↦ ⟨hT, hq⟩⟩
  · refine ⟨_, rfl, (payloadLo_honestCell_node L l level index).trans rfl, fun hq ↦ ?_⟩
    exact absurd hq hT

end xmss

end Quantum.Xmss.Hybrid

end
