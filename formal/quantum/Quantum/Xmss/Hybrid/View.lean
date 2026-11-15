module

public import Quantum.Xmss.HonestTable
public import Quantum.Xmss.Hybrid.Kraus

@[expose] public section

/-!
# The view lemma of the hidden-cell hybrid

The hybrid between runtime 1 and runtime 2 (design, sections 2 and 5.3) costs, at every call of
runtime 2, the mass of the call's input on hidden honest cells. This file bounds those masses on
average over the honest table.

* `sum_queryWeight_le`, `queryWeight_add`: weights whose sum over a finite family is at most `c`
  times the trace give `j`-th call weights whose sum is at most `c` times the trace of the initial
  state; weights add up.
* `avg_queryWeight_le` (**the view lemma, averaged**): reparametrize the uniformly drawn tables
  `θ` by `e : Θ ≃ P × V` into public data `p` and a hidden value `v`. If, on a set `G` of tables,
  the run of runtime 2 up to its `j`-th call is a function of `p` and the weight of that call is a
  weight `w p v` whose sum over `v` is at most `c` times the trace, then the average weight is at
  most `c / |V|` plus the fraction of tables outside `G`.
* `sum_hiddenMass_le`: if every cell lies in the hidden sets of at most `k` members of a family,
  the hidden masses (`Quantum.Xmss.Hybrid.hiddenMass`) of an input add up to at most `k` times its
  trace; `hiddenMass_le`, `hiddenMass_union_le`: the mass is at most the trace and subadditive in
  the hidden sets.
* `avg_hiddenMass_slots_le`: hidden values `v : S → D` of several slots, jointly uniform, and the
  cells `slotCells slot val v` that hold the hidden value of their slot: average mass at most
  `1 / |D|` per call, whatever `|S|`.
* Seed-level cells: `seedCells S₀` (the `k`-cells whose bits `64` to `319` are `S₀`) and
  `seedKeyCells S` (bits `256` to `511` are `S`). The first block of the seed derivation lies in
  `seedCells L.masterSeed` (`firstBlock_seedInput_mem_seedCells`), and the first block of every
  input whose payload starts with the scheme seed (the parameter, the chain starts, the randomizer
  bases) lies in `seedKeyCells L.seed`; it is the first read of hashing the input
  (`head?_inputReads`). A cell lies in these sets for exactly one seed
  (`sum_indicator_seedCells`, `sum_indicator_seedKeyCells`).
* Reparametrization of `S₀` (`seedSplit`): the scheme seed is `out256 (r + h z)` with `r`, `z`
  independent of `h` (`seed_eq_seedRound`); moving `h z` (plus `r`) to a reference cell `zr` is a
  bijection of tables (`seedReparam`) after which the scheme seed is read at `zr`
  (`seed_eq_seedSplit`) and `h` is unchanged off `{z, zr}` (`seedReparam_h_of_ne`), so `S₀` is
  uniform and independent of the public part.
* `avg_hiddenMass_masterSeed_le`, `avg_hiddenMass_schemeSeed_le` (from `avg_hiddenMass_seed_le`):
  the average mass at the seed-level cells is at most `2^-256` per call plus the fraction of tables
  on which the run is not a function of the public part.
-/

open Matrix
open scoped ENNReal ComplexOrder

universe u v w u₁ v₁

namespace Quantum.Xmss.Hybrid

open Quantum QuantumRuntime

/-! ## Averages of query weights -/

section weights

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- Weights add up. -/
theorem queryWeight_add (w₁ w₂ : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec Ω A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    R.queryWeight I (fun i σ ↦ w₁ i σ + w₂ i σ) x ρ j =
      R.queryWeight I w₁ x ρ j + R.queryWeight I w₂ x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => simp
  | primBind _ o k ih =>
    simp only [queryWeight_primBind, ih, ENNReal.tsum_add]
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero => rfl
    | succ j => simp only [queryWeight_queryBind_succ, ih, ENNReal.tsum_add]

/-- **Weights of a finite family.** If the weights `w v` add up, on every positive semidefinite
input, to at most `c` times its trace, the weights of the `j`-th call add up to at most `c` times
the trace of the initial state. -/
theorem sum_queryWeight_le {V : Type*} [Fintype V]
    (w : V → ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞) (c : ℝ≥0∞)
    (hw : ∀ i σ, σ.PosSemidef → ∑ v, w v i σ ≤ c * ENNReal.ofReal σ.trace.re)
    (x : QuantumComp L spec Ω A) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (j : ℕ) : ∑ v, R.queryWeight I (w v) x ρ j ≤ c * ENNReal.ofReal ρ.trace.re := by
  have h := R.tsum_queryWeight I w x ρ j
  rw [tsum_fintype] at h
  rw [h]
  calc R.queryWeight I (fun i σ ↦ ∑' v, w v i σ) x ρ j
      ≤ R.queryWeight I (fun _ σ ↦ c * ENNReal.ofReal σ.trace.re) x ρ j :=
        R.queryWeight_mono I (fun i σ hσ ↦ by rw [tsum_fintype]; exact hw i σ hσ) x hρ j
    _ = c * R.queryWeight I (fun _ σ ↦ ENNReal.ofReal σ.trace.re) x ρ j :=
        R.queryWeight_const_mul I c x ρ j
    _ ≤ c * ENNReal.ofReal ρ.trace.re := by
        gcongr
        exact R.queryWeight_le_ofReal_trace I (fun _ _ _ ↦ le_rfl) x hρ j

/-- **The view lemma, averaged.** Draw the table `θ` uniformly and reparametrize it by
`e : Θ ≃ P × V` into public data and a hidden value, so that the hidden value is uniform and
independent of the public data. Let `f θ` be the weight of the `j`-th call of the run for `θ`. On
the tables of `G`, the run is that of the program `x p` from `ρ p` for the public data `p`, and
`f θ` is at most the `j`-th call weight `w p v`, where the weights `w p v` add up over the hidden
values to at most `c` times the trace; elsewhere `f θ ≤ 1`. Then the average of `f` is at most
`c / |V|` plus the fraction of tables outside `G`. -/
theorem avg_queryWeight_le {Θ P V : Type*} [Fintype Θ] [Fintype P] [Fintype V]
    (e : Θ ≃ P × V) (f : Θ → ℝ≥0∞) (x : P → QuantumComp L spec Ω A)
    (ρ : P → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ p, (ρ p).PosSemidef)
    (hρ₁ : ∀ p, ENNReal.ofReal (ρ p).trace.re ≤ 1)
    (w : P → V → ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞) (c : ℝ≥0∞)
    (hw : ∀ p i σ, σ.PosSemidef → ∑ v, w p v i σ ≤ c * ENNReal.ofReal σ.trace.re) (j : ℕ)
    (G : Finset Θ)
    (hG : ∀ θ ∈ G, f θ ≤ R.queryWeight I (w (e θ).1 (e θ).2) (x (e θ).1) (ρ (e θ).1) j)
    (hB : ∀ θ ∉ G, f θ ≤ 1) :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ θ, f θ ≤
      c * (Fintype.card V : ℝ≥0∞)⁻¹ +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((Fintype.card Θ - G.card : ℕ) : ℝ≥0∞) := by
  classical
  rw [← Finset.card_compl G]
  set g : P × V → ℝ≥0∞ := fun q ↦ R.queryWeight I (w q.1 q.2) (x q.1) (ρ q.1) j
  have hsum : ∑ θ, g (e θ) ≤ Fintype.card P * c := by
    rw [e.sum_comp g, Fintype.sum_prod_type]
    calc ∑ p, ∑ v, g (p, v) ≤ ∑ _p : P, c * 1 := Finset.sum_le_sum fun p _ ↦
          (sum_queryWeight_le R I (w p) c (hw p) (x p) (hρ p) j).trans (by gcongr; exact hρ₁ p)
      _ = Fintype.card P * c := by simp [Finset.card_univ]
  have hf : ∑ θ, f θ ≤ Fintype.card P * c + Gᶜ.card := by
    rw [← Finset.sum_add_sum_compl G f]
    refine add_le_add ((Finset.sum_le_sum hG).trans
      ((Finset.sum_le_sum_of_subset (Finset.subset_univ G)).trans hsum)) ?_
    calc ∑ θ ∈ Gᶜ, f θ ≤ ∑ _θ ∈ Gᶜ, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun θ hθ ↦ hB θ (Finset.mem_compl.mp hθ)
      _ = Gᶜ.card := by simp
  rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  calc ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * ∑ θ, f θ
      ≤ ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * (Fintype.card P * c + Gᶜ.card) := by
        gcongr
    _ = ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * (Fintype.card P * c) +
          ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * Gᶜ.card := mul_add _ _ _
    _ ≤ c * (Fintype.card V : ℝ≥0∞)⁻¹ +
          ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * Gᶜ.card := by
        refine add_le_add ?_ le_rfl
        rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
          (Or.inl (ENNReal.natCast_ne_top _))]
        by_cases hP : (Fintype.card P : ℝ≥0∞) = 0
        · simp [hP]
        · refine le_of_eq ?_
          rw [show (Fintype.card P : ℝ≥0∞)⁻¹ * (Fintype.card V : ℝ≥0∞)⁻¹ * (Fintype.card P * c) =
              ((Fintype.card P : ℝ≥0∞)⁻¹ * Fintype.card P) *
                (c * (Fintype.card V : ℝ≥0∞)⁻¹) by ring,
            ENNReal.inv_mul_cancel hP (ENNReal.natCast_ne_top _), one_mul]

end weights

/-! ## Hidden masses of families of hidden sets -/

section masses

open Quantum.Sponge

/-- The trace of a positive semidefinite operator is the sum of its diagonal entries, in `ℝ≥0∞`. -/
theorem ofReal_trace_re_eq_sum {α : Type} [Fintype α] (σ : Matrix α α ℂ) (hσ : σ.PosSemidef) :
    ENNReal.ofReal σ.trace.re = ∑ a, ENNReal.ofReal (σ a a).re := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  exact ENNReal.ofReal_sum_of_nonneg fun a _ ↦ (Complex.nonneg_iff.mp (hσ.diag_nonneg (i := a))).1

/-- **Masses of a family of sets.** If every basis state lies in the sets `S v` for a total weight
of at most `k` (at most `k` of them), the masses of the sets add up to at most `k` times the
trace. -/
theorem sum_diagMass_le {V α : Type} [Fintype V] [Fintype α] (S : V → Set α) (k : ℝ≥0∞)
    (hS : ∀ a, ∑ v, (S v).indicator (fun _ ↦ (1 : ℝ≥0∞)) a ≤ k) {σ : Matrix α α ℂ}
    (hσ : σ.PosSemidef) : ∑ v, diagMass (S v) σ ≤ k * ENNReal.ofReal σ.trace.re := by
  rw [ofReal_trace_re_eq_sum σ hσ, Finset.mul_sum]
  simp only [diagMass]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  calc ∑ v, (S v).indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a
      = (∑ v, (S v).indicator (fun _ ↦ (1 : ℝ≥0∞)) a) * ENNReal.ofReal (σ a a).re := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        by_cases h : a ∈ S v <;> simp [h]
    _ ≤ k * ENNReal.ofReal (σ a a).re := by gcongr; exact hS a

/-- The mass of a set is at most the trace. -/
theorem diagMass_le {α : Type} [Fintype α] (S : Set α) {σ : Matrix α α ℂ} (hσ : σ.PosSemidef) :
    diagMass S σ ≤ ENNReal.ofReal σ.trace.re := by
  have h := sum_diagMass_le (V := Unit) (fun _ ↦ S) 1 (fun a ↦ by
    by_cases ha : a ∈ S <;> simp [ha]) hσ
  simpa using h

/-- The mass of a union is at most the sum of the masses. -/
theorem diagMass_union_le {α : Type} [Fintype α] (S T : Set α) (σ : Matrix α α ℂ) :
    diagMass (S ∪ T) σ ≤ diagMass S σ + diagMass T σ := by
  simp only [diagMass, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  by_cases hS : a ∈ S <;> by_cases hT : a ∈ T <;> simp [hS, hT]

/-- The mass is monotone in the set. -/
theorem diagMass_mono {α : Type} [Fintype α] {S T : Set α} (h : S ⊆ T) (σ : Matrix α α ℂ) :
    diagMass S σ ≤ diagMass T σ :=
  Finset.sum_le_sum fun _ _ ↦ Set.indicator_le_indicator_of_subset h (fun _ ↦ by simp) _

/-- The multiplicity of a family of sets bounds that of a family of sets mapped into it. -/
theorem sum_indicator_le_of_mem {V α β : Type} [Fintype V] {S : V → Set α} {T : V → Set β}
    (g : α → β) (hST : ∀ v a, a ∈ S v → g a ∈ T v) {k : ℝ≥0∞}
    (hT : ∀ b, ∑ v, (T v).indicator (fun _ ↦ (1 : ℝ≥0∞)) b ≤ k) (a : α) :
    ∑ v, (S v).indicator (fun _ ↦ (1 : ℝ≥0∞)) a ≤ k := by
  refine (Finset.sum_le_sum fun v _ ↦ ?_).trans (hT (g a))
  by_cases h : a ∈ S v
  · simp [h, hST v a h]
  · simp [h]

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

/-- **Hidden masses of a family of hidden sets.** If every cell lies in the hidden sets of at most
`k` members of the family (in weight), the hidden masses of an input add up to at most `k` times
its trace, at every port. -/
theorem sum_hiddenMass_le {V : Type} [Fintype V] (Hh : V → Set Z) (Hk Hk' : V → Set X)
    (k : ℝ≥0∞) (hh : ∀ z, ∑ v, (Hh v).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ k)
    (hk : ∀ x, ∑ v, (Hk v).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ k)
    (hk' : ∀ x, ∑ v, (Hk' v).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ k)
    (i : (hwSpec X Z M).Port)
    {σ : Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ} (hσ : σ.PosSemidef) :
    ∑ v, hiddenMass (M := M) (Hh v) (Hk v) (Hk' v) i σ ≤ k * ENNReal.ofReal σ.trace.re := by
  rcases i with ((_ | _ | _) | (⟨z, upd⟩ | ⟨x, upd⟩ | ⟨x, upd⟩)) | c
  · exact sum_diagMass_le
      (fun v ↦ {p : (Z × X) × HwReg X Z M | p.1.1 ∈ Hh v ∧ p.2.2.1.1 p.1.1 = none}) k
      (sum_indicator_le_of_mem (fun p ↦ p.1.1) (fun _ _ hp ↦ hp.1) hh) hσ
  · exact sum_diagMass_le
      (fun v ↦ {p : (X × Z) × HwReg X Z M | p.1.1 ∈ Hk v ∧ p.2.2.1.2.1 p.1.1 = none}) k
      (sum_indicator_le_of_mem (fun p ↦ p.1.1) (fun _ _ hp ↦ hp.1) hk) hσ
  · exact sum_diagMass_le
      (fun v ↦ {p : (X × Z) × HwReg X Z M | p.1.1 ∈ Hk' v ∧ p.2.2.1.2.2 p.1.1 = none}) k
      (sum_indicator_le_of_mem (fun p ↦ p.1.1) (fun _ _ hp ↦ hp.1) hk') hσ
  · exact sum_diagMass_le
      (fun v ↦ {p : Unit × HwReg X Z M | z ∈ Hh v ∧ p.2.2.1.1 z = none}) k
      (sum_indicator_le_of_mem (fun _ ↦ z) (fun _ _ hp ↦ hp.1) hh) hσ
  · exact sum_diagMass_le
      (fun v ↦ {p : Unit × HwReg X Z M | x ∈ Hk v ∧ p.2.2.1.2.1 x = none}) k
      (sum_indicator_le_of_mem (fun _ ↦ x) (fun _ _ hp ↦ hp.1) hk) hσ
  · exact sum_diagMass_le
      (fun v ↦ {p : Unit × HwReg X Z M | x ∈ Hk' v ∧ p.2.2.1.2.2 x = none}) k
      (sum_indicator_le_of_mem (fun _ ↦ x) (fun _ _ hp ↦ hp.1) hk') hσ
  · simp [hiddenMass]

/-- The hidden mass of an input is at most its trace. -/
theorem hiddenMass_le (Hh : Set Z) (Hk Hk' : Set X) (i : (hwSpec X Z M).Port)
    {σ : Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ} (hσ : σ.PosSemidef) :
    hiddenMass (M := M) Hh Hk Hk' i σ ≤ ENNReal.ofReal σ.trace.re := by
  have hu : ∀ {β : Type} (H : Set β) (b : β),
      ∑ _v : Unit, H.indicator (fun _ ↦ (1 : ℝ≥0∞)) b ≤ 1 := fun H b ↦ by
    by_cases hb : b ∈ H <;> simp [hb]
  simpa using sum_hiddenMass_le (V := Unit) (M := M) (fun _ ↦ Hh) (fun _ ↦ Hk) (fun _ ↦ Hk') 1
    (hu Hh) (hu Hk) (hu Hk') i hσ

/-- **Hidden masses split over unions** of hidden sets. -/
theorem hiddenMass_union_le (Hh₁ Hh₂ : Set Z) (Hk₁ Hk₂ Hk'₁ Hk'₂ : Set X)
    (i : (hwSpec X Z M).Port)
    (σ : Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ) :
    hiddenMass (M := M) (Hh₁ ∪ Hh₂) (Hk₁ ∪ Hk₂) (Hk'₁ ∪ Hk'₂) i σ ≤
      hiddenMass Hh₁ Hk₁ Hk'₁ i σ + hiddenMass Hh₂ Hk₂ Hk'₂ i σ := by
  rcases i with ((_ | _ | _) | (⟨z, upd⟩ | ⟨x, upd⟩ | ⟨x, upd⟩)) | c <;>
    first
    | refine (diagMass_mono ?_ σ).trans (diagMass_union_le _ _ σ)
      rintro p ⟨hp | hp, hW⟩
      · exact Or.inl ⟨hp, hW⟩
      · exact Or.inr ⟨hp, hW⟩
    | simp [hiddenMass]

end masses

/-! ## Several hidden values at once -/

section slots

open Quantum.Sponge

/-- The cells holding hidden values `v : S → D`: a cell names at most one slot, `slot x`, and it is
hidden when the value it holds, `val x`, is that slot's hidden value. -/
def slotCells {α S D : Type} (slot : α → Option S) (val : α → D) (v : S → D) : Set α :=
  {x | ∃ s, slot x = some s ∧ val x = v s}

/-- A cell holds the hidden value of its slot for `|D| ^ (|S| - 1)` of the `|D| ^ |S|` families of
hidden values. -/
theorem sum_indicator_slotCells {α S D : Type} [Fintype S] [DecidableEq S] [Fintype D]
    [DecidableEq D] (slot : α → Option S) (val : α → D) (a : α) :
    ∑ v : S → D, (slotCells slot val v).indicator (fun _ ↦ (1 : ℝ≥0∞)) a ≤
      (Fintype.card D : ℝ≥0∞) ^ (Fintype.card S - 1) := by
  rcases h : slot a with _ | s
  · simp [slotCells, h]
  · have hmem : ∀ v : S → D, a ∈ slotCells slot val v ↔ v s = val a := fun v ↦
      ⟨fun ⟨s', hs', hv⟩ ↦ by
        rw [h, Option.some.injEq] at hs'
        rw [hs', hv],
        fun hv ↦ ⟨s, h, hv.symm⟩⟩
    have hind : ∀ v : S → D, (slotCells slot val v).indicator (fun _ ↦ (1 : ℝ≥0∞)) a =
        if v s = val a then 1 else 0 := fun v ↦ by
      by_cases hv : v s = val a
      · rw [Set.indicator_of_mem ((hmem v).mpr hv)]
        simp [hv]
      · rw [Set.indicator_of_notMem fun h' ↦ hv ((hmem v).mp h')]
        simp [hv]
    rw [Finset.sum_congr rfl fun v _ ↦ hind v, Fintype.sum_equiv (Equiv.funSplitAt s D)
      (fun v : S → D ↦ if v s = val a then (1 : ℝ≥0∞) else 0)
      (fun q ↦ if q.1 = val a then (1 : ℝ≥0∞) else 0) fun v ↦ rfl, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (val a) (fun b _ hb ↦ by simp [hb]) (by simp)]
    simp only [↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_fun, Nat.cast_pow]
    rw [show Fintype.card {j // j ≠ s} = Fintype.card S - 1 by simp]

/-- `|D| ^ (n - 1) / |D| ^ n = 1 / |D|`. -/
theorem pow_pred_mul_inv_pow {d : ℝ≥0∞} (hd : d ≠ 0) (hd' : d ≠ ⊤) {n : ℕ} (hn : 1 ≤ n) :
    d ^ (n - 1) * (d ^ n)⁻¹ = d⁻¹ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, ENNReal.mul_inv (Or.inl (pow_ne_zero _ hd))
    (Or.inl (ENNReal.pow_ne_top hd')), ← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero _ hd) (ENNReal.pow_ne_top hd'), one_mul]

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {M : Type} [Fintype M] [DecidableEq M] {Λ : LocalSig.{u, v}} (I : Λ.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **The view lemma for jointly hidden values.** Reparametrize the uniformly drawn tables by
`e : Θ ≃ P × (S → D)` into public data and the hidden values of the slots `S`, jointly uniform and
independent of the public data. Let the hidden `k`-cells be `slotCells slot val v`: a cell names at
most one slot and is hidden when it holds that slot's hidden value. If, on `G`, the run is a
function of the public data, the hidden mass of the `j`-th call of runtime 2, averaged over the
tables, is at most `1 / |D|` plus the fraction of tables outside `G`, however many slots. -/
theorem avg_hiddenMass_slots_le {Θ P S D : Type} [Fintype Θ] [Fintype P] [Fintype S]
    [DecidableEq S] [Nonempty S] [Fintype D] [DecidableEq D] [Nonempty D]
    (e : Θ ≃ P × (S → D)) (slot : X → Option S) (val : X → D) (m₀ : M)
    (xθ : Θ → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρθ : Θ → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρθ : ∀ θ, (ρθ θ).PosSemidef) (hρθ₁ : ∀ θ, ENNReal.ofReal (ρθ θ).trace.re ≤ 1)
    (x : P → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : P → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ p, (ρ p).PosSemidef) (hρ₁ : ∀ p, ENNReal.ofReal (ρ p).trace.re ≤ 1)
    (G : Finset Θ) (hG : ∀ θ ∈ G, xθ θ = x (e θ).1 ∧ ρθ θ = ρ (e θ).1) (j : ℕ) :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ θ, (runtime2 X Z m₀).queryWeight I
        (hiddenMass ∅ (slotCells slot val (e θ).2) ∅) (xθ θ) (ρθ θ) j ≤
      (Fintype.card D : ℝ≥0∞)⁻¹ +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((Fintype.card Θ - G.card : ℕ) : ℝ≥0∞) := by
  have hw : ∀ (_ : P) i σ, σ.PosSemidef →
      ∑ v, hiddenMass (M := M) ∅ (slotCells slot val v) ∅ i σ ≤
        (Fintype.card D : ℝ≥0∞) ^ (Fintype.card S - 1) * ENNReal.ofReal σ.trace.re :=
    fun _ i σ hσ ↦ sum_hiddenMass_le (M := M) (fun _ ↦ (∅ : Set Z)) (slotCells slot val)
      (fun _ ↦ (∅ : Set X)) _ (fun _ ↦ by simp) (sum_indicator_slotCells slot val)
      (fun _ ↦ by simp) i (σ := σ) hσ
  have h := avg_queryWeight_le (runtime2 X Z m₀) I e
    (fun θ ↦ (runtime2 X Z m₀).queryWeight I (hiddenMass ∅ (slotCells slot val (e θ).2) ∅)
      (xθ θ) (ρθ θ) j)
    x ρ hρ hρ₁ (fun _ v ↦ hiddenMass ∅ (slotCells slot val v) ∅) _ hw j G
    (fun θ hθ ↦ by rw [(hG θ hθ).1, (hG θ hθ).2])
    (fun θ _ ↦ ((runtime2 X Z m₀).queryWeight_le_ofReal_trace I
      (fun i _ hσ ↦ hiddenMass_le _ _ _ i hσ) _ (hρθ θ) j).trans (hρθ₁ θ))
  rwa [Fintype.card_fun, Nat.cast_pow, pow_pred_mul_inv_pow (by simp) (by simp)
    Fintype.card_pos] at h

end slots

/-! ## Seed-level cells -/

section seed

open HashSig LeanXmss Quantum.Sponge

/-- The `k`-cells whose bits `64` to `319` are `S₀`: those that hold the master seed where the
seed derivation `"leanXMSS" ‖ S₀` puts it. -/
def seedCells (S₀ : MasterSeed) : Set X :=
  {x | rateSlice x 64 256 (by norm_num) = S₀}

/-- The `k`-cells whose bits `256` to `511` are `S`: those that hold the scheme seed where an input
`P ‖ A ‖ S ‖ …` puts it. -/
def seedKeyCells (S : MasterSeed) : Set X :=
  {x | rateSlice x 256 256 (by norm_num) = S}

/-- A cell lies in `seedCells S₀` for exactly one master seed. -/
theorem sum_indicator_seedCells (x : X) :
    ∑ S₀, (seedCells S₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) x = 1 := by
  classical
  simp only [Set.indicator_apply, seedCells, Set.mem_ofPred_eq]
  rw [Finset.sum_ite_eq]
  simp

/-- A cell lies in `seedKeyCells S` for exactly one scheme seed. -/
theorem sum_indicator_seedKeyCells (x : X) :
    ∑ S, (seedKeyCells S).indicator (fun _ ↦ (1 : ℝ≥0∞)) x = 1 := by
  classical
  simp only [Set.indicator_apply, seedKeyCells, Set.mem_ofPred_eq]
  rw [Finset.sum_ite_eq]
  simp

/-- The first block of the seed derivation `"leanXMSS" ‖ S₀` lies in `seedCells S₀`. -/
theorem firstBlock_seedInput_mem_seedCells (S₀ : MasterSeed) :
    blockOf (firstBlock (seedTag ++ littleEndianBytes 32 S₀)) ∈ seedCells S₀ := by
  have hlen : (seedTag ++ littleEndianBytes 32 S₀).length = 40 := by
    rw [List.length_append, show seedTag.length = 8 from rfl, length_littleEndianBytes]
  refine rateSlice_eq fun j hj ↦ ?_
  rw [blockOf_firstBlock _ _ (by rw [hlen]; change 64 + j < 8 * 40; omega), Fin.val_mk,
    show 64 + j = 8 * seedTag.length + j from rfl, inputBit_append_right,
    inputBit_littleEndianBytes]

/-- The first block of an input `P ‖ A ‖ S ‖ rest` lies in `seedKeyCells S`. -/
theorem firstBlock_thInput_mem_seedKeyCells (Q : PublicParameter) (fields : TweakFields)
    (S : MasterSeed) (rest : HashInput) :
    blockOf (firstBlock (thInput Q fields (littleEndianBytes 32 S ++ rest))) ∈ seedKeyCells S := by
  have hlen : 64 ≤ (thInput Q fields (littleEndianBytes 32 S ++ rest)).length := by
    rw [length_thInput, List.length_append, length_littleEndianBytes]
    omega
  refine rateSlice_eq fun j hj ↦ ?_
  rw [blockOf_firstBlock _ _ (by change 256 + j < _; omega), Fin.val_mk,
    inputBit_thInput_payload,
    inputBit_append_left _ _ _ (by rw [length_littleEndianBytes]; omega),
    inputBit_littleEndianBytes]

/-- The first block of an input `P ‖ A ‖ S` lies in `seedKeyCells S`. -/
theorem firstBlock_thInput_seed_mem_seedKeyCells (Q : PublicParameter) (fields : TweakFields)
    (S : MasterSeed) :
    blockOf (firstBlock (thInput Q fields (littleEndianBytes 32 S))) ∈ seedKeyCells S := by
  simpa using firstBlock_thInput_mem_seedKeyCells Q fields S []

/-- The first read of the sponge evaluation of a message is `k` at its first block. -/
theorem head?_spongeReads (π : Equiv.Perm (X × Z)) (h : Z → X) (k k' : X → Z) (b : X)
    (m : List X) : (spongeReads π h k k' (b :: m)).head? = some (.k b (k b)) := by
  rw [spongeReads, List.foldl_cons,
    show logStep π h k k' ((0, 0), []) b = (_, roundReads π h k k' (0, 0) b) from rfl,
    snd_foldl_logStep (h, k, k') π]
  simp [roundReads]

/-- The first read of hashing an input is `k` at its first block. -/
theorem head?_inputReads (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (input : HashInput) :
    (inputReads t π input).head? =
      some (.k (blockOf (firstBlock input)) (t.2.1 (blockOf (firstBlock input)))) := by
  obtain ⟨m, hm⟩ : ∃ m, blocks input = blockOf (firstBlock input) :: m := by
    have hh := head?_blocks input
    cases hb : blocks input with
    | nil => rw [hb] at hh; simp at hh
    | cons b m =>
      rw [hb, List.head?_cons, Option.some.injEq] at hh
      exact ⟨m, by rw [hh]⟩
  rw [inputReads, hm, head?_spongeReads]

namespace HonestTable

variable (L : HonestTable)

/-- The first `k`-cell of the seed derivation of an honest table holds its master seed. -/
theorem seedInput_cell_mem :
    blockOf (firstBlock (seedTag ++ littleEndianBytes 32 L.masterSeed)) ∈
      seedCells L.masterSeed :=
  firstBlock_seedInput_mem_seedCells _

/-- The first `k`-cell of the parameter's derivation holds the scheme seed. -/
theorem paramInput_cell_mem :
    blockOf (firstBlock (thInput 0 (keygenDomainFields .parameter)
      (littleEndianBytes 32 L.seed))) ∈ seedKeyCells L.seed :=
  firstBlock_thInput_seed_mem_seedKeyCells _ _ _

/-- The first `k`-cell of a chain-start derivation holds the scheme seed. -/
theorem chainStartInput_cell_mem (l : Layer) (e : KeyIndex) (pair : ChainPairIndex) :
    blockOf (firstBlock (thInput L.param (keygenDomainFields (.oneTimeChainPair l e pair))
      (littleEndianBytes 32 L.seed))) ∈ seedKeyCells L.seed :=
  firstBlock_thInput_seed_mem_seedKeyCells _ _ _

/-- The first `k`-cell of a randomizer-base derivation holds the scheme seed. -/
theorem randomizerBaseInput_cell_mem (l : Layer) (e : KeyIndex) (message : HashInput) :
    blockOf (firstBlock (thInput L.param (tweakFields 7 0 (layerHi l 0) e)
      (littleEndianBytes 32 L.seed ++ message))) ∈ seedKeyCells L.seed :=
  firstBlock_thInput_mem_seedKeyCells _ _ _ _

end HonestTable

/-! ## The master seed, reparametrized by the scheme seed -/

/-- The first block of the seed derivation `"leanXMSS" ‖ S₀`. -/
def seedCell (S₀ : MasterSeed) : X :=
  blockOf (firstBlock (seedTag ++ littleEndianBytes 32 S₀))

/-- The seed derivation is one block. -/
theorem blocks_seedInput (S₀ : MasterSeed) :
    blocks (seedTag ++ littleEndianBytes 32 S₀) = [seedCell S₀] := by
  have hl := length_blocks (seedTag ++ littleEndianBytes 32 S₀)
  have hh := head?_blocks (seedTag ++ littleEndianBytes 32 S₀)
  rw [List.length_append, show seedTag.length = 8 from rfl, length_littleEndianBytes] at hl
  cases hb : blocks (seedTag ++ littleEndianBytes 32 S₀) with
  | nil => rw [hb] at hh; simp at hh
  | cons b m =>
    rw [hb, List.length_cons] at hl
    rw [hb, List.head?_cons, Option.some.injEq] at hh
    rw [List.eq_nil_of_length_eq_zero (l := m) (by omega), hh]
    rfl

/-- The round of the seed derivation from `(b₀, 0)` up to `h`: the rate after `π` and `σ_k'`, and
the capacity at which `h` is read. It does not involve `h`. -/
def seedRound (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed) : X × Z :=
  ((π (seedCell S₀, k (seedCell S₀))).1,
    (π (seedCell S₀, k (seedCell S₀))).2 + k' (π (seedCell S₀, k (seedCell S₀))).1)

/-- **The scheme seed is the output of one fresh `h` cell**: `S = out256 (r + h z)` for the rate
`r` and the capacity `z` of `seedRound`, which do not involve `h`. -/
theorem seed_eq_seedRound (L : HonestTable) :
    L.seed = out256 ((seedRound L.keys.2.1 L.keys.2.2 L.perm L.masterSeed).1 +
      L.keys.1 (seedRound L.keys.2.1 L.keys.2.2 L.perm L.masterSeed).2) := by
  show out256 (spongeHash (spongePerm L.keys L.perm)
    (blocks (seedTag ++ littleEndianBytes 32 L.masterSeed))) = _
  rw [blocks_seedInput]
  simp only [spongeHash, absorb, List.foldl_cons, List.foldl_nil, absorbStep, spongePerm,
    Equiv.Perm.mul_apply, rateRound_apply, capacityRound_apply, zero_add, seedRound]

/-- Move the value of `h` at `z₀` to the reference cell `zr`, adding `r`. -/
def reparamH (r : X) (z₀ zr : Z) (h : Z → X) : Z → X :=
  fun z ↦ h (Equiv.swap z₀ zr z) + if z = zr then r else 0

/-- The inverse of `reparamH r z₀ zr`. -/
def unreparamH (r : X) (z₀ zr : Z) (h : Z → X) : Z → X :=
  fun z ↦ h (Equiv.swap z₀ zr z) - if Equiv.swap z₀ zr z = zr then r else 0

theorem unreparamH_reparamH (r : X) (z₀ zr : Z) (h : Z → X) :
    unreparamH r z₀ zr (reparamH r z₀ zr h) = h := by
  funext z
  simp [reparamH, unreparamH]

theorem reparamH_unreparamH (r : X) (z₀ zr : Z) (h : Z → X) :
    reparamH r z₀ zr (unreparamH r z₀ zr h) = h := by
  funext z
  simp [reparamH, unreparamH]

/-- **The seed reparametrization** at the reference cell `zr`: the table whose `h` holds, at `zr`,
the output `r + h z` of the seed derivation's round (`seedRound`), and the old value at `zr` at
`z`; `k`, `k'`, `π` and `S₀` are unchanged, so `r` and `z` are those of the new table too. A
bijection, so it maps the uniform table to the uniform table. -/
def seedReparam (zr : Z) : HonestTable ≃ HonestTable where
  toFun L := ⟨(reparamH (seedRound L.keys.2.1 L.keys.2.2 L.perm L.masterSeed).1
    (seedRound L.keys.2.1 L.keys.2.2 L.perm L.masterSeed).2 zr L.keys.1, L.keys.2), L.perm,
    L.masterSeed⟩
  invFun L := ⟨(unreparamH (seedRound L.keys.2.1 L.keys.2.2 L.perm L.masterSeed).1
    (seedRound L.keys.2.1 L.keys.2.2 L.perm L.masterSeed).2 zr L.keys.1, L.keys.2), L.perm,
    L.masterSeed⟩
  left_inv L := by
    rcases L with ⟨⟨h, k, k'⟩, π, S₀⟩
    simp only [unreparamH_reparamH]
  right_inv L := by
    rcases L with ⟨⟨h, k, k'⟩, π, S₀⟩
    simp only [reparamH_unreparamH]

/-- In the reparametrized table, the scheme seed is read off the reference cell. -/
theorem seed_eq_seedReparam (zr : Z) (L : HonestTable) :
    L.seed = out256 ((seedReparam zr L).keys.1 zr) := by
  rw [seed_eq_seedRound]
  simp only [seedReparam, Equiv.coe_fn_mk, reparamH, Equiv.swap_apply_right, ↓reduceIte]
  rw [add_comm]

/-- The reparametrization changes `h` only at the seed derivation's cell and the reference cell. -/
theorem seedReparam_h_of_ne (zr : Z) (L : HonestTable) {z : Z}
    (h₀ : z ≠ (seedRound L.keys.2.1 L.keys.2.2 L.perm L.masterSeed).2) (hr : z ≠ zr) :
    (seedReparam zr L).keys.1 z = L.keys.1 z := by
  simp only [seedReparam, Equiv.coe_fn_mk, reparamH, Equiv.swap_apply_of_ne_of_ne h₀ hr, hr,
    ↓reduceIte, add_zero]

theorem seedReparam_keys_snd (zr : Z) (L : HonestTable) :
    (seedReparam zr L).keys.2 = L.keys.2 := by
  simp only [seedReparam, Equiv.coe_fn_mk]

theorem seedReparam_perm (zr : Z) (L : HonestTable) : (seedReparam zr L).perm = L.perm := by
  simp only [seedReparam, Equiv.coe_fn_mk]

theorem seedReparam_masterSeed (zr : Z) (L : HonestTable) :
    (seedReparam zr L).masterSeed = L.masterSeed := by
  simp only [seedReparam, Equiv.coe_fn_mk]

/-- The honest table as its fields. -/
def tableEquiv : HonestTable ≃ (SpongeKeys X Z × Equiv.Perm (X × Z)) × MasterSeed where
  toFun L := ((L.keys, L.perm), L.masterSeed)
  invFun q := ⟨q.1.1, q.1.2, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype HonestTable :=
  Fintype.ofEquiv _ tableEquiv.symm

/-- **The table split into public data and the master seed**: the reparametrized keys and `π`,
and `S₀`. Uniform tables are uniform pairs, so `S₀` is uniform and independent of the public part,
which determines the scheme seed (`seed_eq_seedSplit`). -/
def seedSplit (zr : Z) : HonestTable ≃ (SpongeKeys X Z × Equiv.Perm (X × Z)) × MasterSeed :=
  (seedReparam zr).trans tableEquiv

theorem seedSplit_snd (zr : Z) (L : HonestTable) : (seedSplit zr L).2 = L.masterSeed := by
  simp only [seedSplit, Equiv.trans_apply, tableEquiv, Equiv.coe_fn_mk, seedReparam_masterSeed]

/-- The scheme seed is a function of the public part of `seedSplit`. -/
theorem seed_eq_seedSplit (zr : Z) (L : HonestTable) :
    L.seed = out256 ((seedSplit zr L).1.1.1 zr) := by
  rw [seed_eq_seedReparam zr]
  simp only [seedSplit, Equiv.trans_apply, tableEquiv, Equiv.coe_fn_mk]

/-! ## The seed-level mass bounds -/

section bound

variable {M : Type} [Fintype M] [DecidableEq M] {Λ : LocalSig.{u, v}} (I : Λ.Interp)
  {Ω : QReg → Type w} {A : QReg}

theorem card_masterSeed : Fintype.card MasterSeed = 2 ^ 256 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

/-- **The seed-level view lemma.** Reparametrize the uniformly drawn tables `θ` by
`e : Θ ≃ P × MasterSeed` into public data and a hidden seed, and let `hid S` be hidden `k`-cells
each of which belongs to `hid S` for at most one seed `S`. If, on the tables of `G`, the run is the
program `x p` from `ρ p` for the public data `p`, then the hidden mass of the `j`-th call of the
run against runtime 2 at the cells `hid S` of the table's seed, averaged over the tables, is at
most `2^-256` plus the fraction of tables outside `G`. -/
theorem avg_hiddenMass_seed_le {Θ P : Type*} [Fintype Θ] [Fintype P]
    (e : Θ ≃ P × MasterSeed) (hid : MasterSeed → Set X)
    (hhid : ∀ x, ∑ S, (hid S).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ 1) (m₀ : M)
    (xθ : Θ → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρθ : Θ → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρθ : ∀ θ, (ρθ θ).PosSemidef) (hρθ₁ : ∀ θ, ENNReal.ofReal (ρθ θ).trace.re ≤ 1)
    (x : P → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : P → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ p, (ρ p).PosSemidef) (hρ₁ : ∀ p, ENNReal.ofReal (ρ p).trace.re ≤ 1)
    (G : Finset Θ) (hG : ∀ θ ∈ G, xθ θ = x (e θ).1 ∧ ρθ θ = ρ (e θ).1) (j : ℕ) :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ θ, (runtime2 X Z m₀).queryWeight I
        (hiddenMass ∅ (hid (e θ).2) ∅) (xθ θ) (ρθ θ) j ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((Fintype.card Θ - G.card : ℕ) : ℝ≥0∞) := by
  have hw : ∀ (_ : P) i σ, σ.PosSemidef →
      ∑ S, hiddenMass (M := M) ∅ (hid S) ∅ i σ ≤ 1 * ENNReal.ofReal σ.trace.re :=
    fun _ i σ hσ ↦ sum_hiddenMass_le (M := M) (fun _ ↦ (∅ : Set Z)) hid (fun _ ↦ (∅ : Set X)) 1
      (fun _ ↦ by simp) hhid (fun _ ↦ by simp) i (σ := σ) hσ
  have h := avg_queryWeight_le (runtime2 X Z m₀) I e
    (fun θ ↦ (runtime2 X Z m₀).queryWeight I (hiddenMass ∅ (hid (e θ).2) ∅) (xθ θ) (ρθ θ) j)
    x ρ hρ hρ₁ (fun _ S ↦ hiddenMass ∅ (hid S) ∅) 1 hw j G
    (fun θ hθ ↦ by rw [(hG θ hθ).1, (hG θ hθ).2])
    (fun θ _ ↦ ((runtime2 X Z m₀).queryWeight_le_ofReal_trace I
      (fun i _ hσ ↦ hiddenMass_le _ _ _ i hσ) _ (hρθ θ) j).trans (hρθ₁ θ))
  rwa [one_mul, card_masterSeed, Nat.cast_pow, Nat.cast_ofNat] at h

/-- **The master-seed cell.** With the tables split by `seedSplit zr` (the reparametrized keys
and `π` public, `S₀` hidden), if on `G` the run is a function of the public part, the mass of the
`j`-th call of runtime 2 at the cells `seedCells S₀`, which contain the seed derivation's first
block, averaged over the uniform table, is at most `2^-256` plus the fraction of tables outside
`G`. -/
theorem avg_hiddenMass_masterSeed_le (zr : Z) (m₀ : M)
    (xθ : HonestTable → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρθ : HonestTable → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρθ : ∀ L, (ρθ L).PosSemidef) (hρθ₁ : ∀ L, ENNReal.ofReal (ρθ L).trace.re ≤ 1)
    (x : SpongeKeys X Z × Equiv.Perm (X × Z) → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : SpongeKeys X Z × Equiv.Perm (X × Z) →
      Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ p, (ρ p).PosSemidef) (hρ₁ : ∀ p, ENNReal.ofReal (ρ p).trace.re ≤ 1)
    (G : Finset HonestTable)
    (hG : ∀ L ∈ G, xθ L = x (seedSplit zr L).1 ∧ ρθ L = ρ (seedSplit zr L).1) (j : ℕ) :
    (Fintype.card HonestTable : ℝ≥0∞)⁻¹ * ∑ L, (runtime2 X Z m₀).queryWeight I
        (hiddenMass ∅ (seedCells L.masterSeed) ∅) (xθ L) (ρθ L) j ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ + (Fintype.card HonestTable : ℝ≥0∞)⁻¹ *
        ((Fintype.card HonestTable - G.card : ℕ) : ℝ≥0∞) := by
  have h := avg_hiddenMass_seed_le I (seedSplit zr) seedCells
    (fun x ↦ (sum_indicator_seedCells x).le) m₀ xθ ρθ hρθ hρθ₁ x ρ hρ hρ₁ G hG j
  simpa only [seedSplit_snd] using h

/-- **The scheme-seed cells.** For a reparametrization `e` whose hidden coordinate is the scheme
seed, the mass of the `j`-th call of runtime 2 at the cells `seedKeyCells S` (which contain the
first blocks of the parameter's, the chain starts' and the randomizer bases' derivations) is at
most `2^-256` on average, plus the fraction of tables outside `G`. -/
theorem avg_hiddenMass_schemeSeed_le {Θ P : Type*} [Fintype Θ] [Fintype P]
    (e : Θ ≃ P × MasterSeed) (m₀ : M) (xθ : Θ → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρθ : Θ → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρθ : ∀ θ, (ρθ θ).PosSemidef) (hρθ₁ : ∀ θ, ENNReal.ofReal (ρθ θ).trace.re ≤ 1)
    (x : P → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : P → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ p, (ρ p).PosSemidef) (hρ₁ : ∀ p, ENNReal.ofReal (ρ p).trace.re ≤ 1)
    (G : Finset Θ) (hG : ∀ θ ∈ G, xθ θ = x (e θ).1 ∧ ρθ θ = ρ (e θ).1) (j : ℕ) :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ θ, (runtime2 X Z m₀).queryWeight I
        (hiddenMass ∅ (seedKeyCells (e θ).2) ∅) (xθ θ) (ρθ θ) j ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((Fintype.card Θ - G.card : ℕ) : ℝ≥0∞) :=
  avg_hiddenMass_seed_le I e seedKeyCells (fun x ↦ (sum_indicator_seedKeyCells x).le) m₀
    xθ ρθ hρθ hρθ₁ x ρ hρ hρ₁ G hG j

end bound

end seed

end Quantum.Xmss.Hybrid

end
