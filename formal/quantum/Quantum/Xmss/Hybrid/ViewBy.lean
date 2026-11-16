module

public import Quantum.Xmss.Hybrid.Disclose
public import VCVio.Quantum.Comp.Simulation

@[expose] public section

/-!
# The lazy-sampling property from template programs

The lazy-sampling hypothesis `ViewBy` of `Quantum.Xmss.Hybrid.Disclose`, for runtime 2 running a
program family in which the hidden values `v : (s : S) → D s` enter only through the cells and
values of program ports, each a function of the restriction of `v` to coordinates `T`.

**The generic statement.** A family of operators indexed by `v` is *lazy* for a labelling `lab` of
the basis (`Lazy`) if its entry at `(a, b)` depends on `v` only through `v` on `lab a ∪ lab b`.
For a family of runtimes `famRuntime init step v` on one register `Dr` labelled by
`lab : Dr → Finset S`, `StepLazy` asks every branch of port `i` to preserve laziness on families
supported on the register states labelled above `need i` (`LazyMap`, `SuppAt`); a Kraus map does
so if its entries never lower the label and, on inputs labelled above `need i`, depend on `v` only
through the label of the output (`lazyMap_conj`).

* `queryWeight_eq_of_lazy` (**the view of a lazy runtime**): by induction over the template program
  `y` (local operations act beside the register, a call relabels, applies the framed step, and
  relabels back), if the initial states are lazy and every call receives an operator supported
  above `need i` (`CallSupp`, as VCVio's `ForallQueries`), the `j`-th call weights agree at hidden
  values agreeing on `T`, for weights reading only the entries labelled inside `T`;
  `queryWeight_diagMass_eq_of_lazy` for diagonal masses of sets labelled `T`.
* `ViewByOn`: `ViewBy` for the weights vanishing outside a set of ports; `ViewBy.viewByOn`.

**Runtime 2.** The label `lab : Hw X Z × M → Finset S` reads the classical data (the hardwired
cells and the memory); hardwiring a cell must never lower it. A template program over
`lazySpec X Z M lab D good` calls the sponge ports, the read ports whose memory update never lowers
the label (`ReadMono`), and template program ports `LazyProg` (cell and value functions of
`restrictTo T v`) satisfying `good`; `realize v y` (a lens) replaces each template program port by
the program port it realizes at `v`, and `queryWeight_realize` runs it against runtime 2 as the
template against `lazyStep m₀ v`. `stepLazy_lazyStep`: the template runtime is lazy, since the
sponge ports act block by block on the classical data and a program port's Kraus operators depend on
`v` only through its coordinates.

* `viewBy_runtime2_realize`: `ViewBy` of runtime 2 for the realized programs, if every template
  program port is called on states whose label already contains its coordinates (a `ForallQueries`
  hypothesis on the template run). This is needed for `ViewBy` as stated: the port called is
  itself a function of `v`, and `ViewBy` asks for every weight on the program ports.
* `viewByOn_runtime2_realize`: with self-disclosing program ports (`SelfDisc`: hardwiring the cell
  records its coordinates in the label), `ViewByOn` for the weights vanishing on the program ports,
  with no hypothesis on the run. The hidden masses of `Disclose` vanish on the program ports.
-/

open Matrix
open scoped ENNReal ComplexOrder

universe u v w u₁ v₁

namespace Quantum.Xmss.Hybrid

open Quantum QuantumRuntime

/-! ## Lazy families of operators -/

section lazy

variable {S : Type} [DecidableEq S] {D : S → Type}

omit [DecidableEq S] in
theorem Agree.mono {T T' : Finset S} (h : T ⊆ T') {v v' : (s : S) → D s} (hv : Agree T' v v') :
    Agree T v v' :=
  fun s hs ↦ hv s (h hs)

/-- A family of operators indexed by the hidden values is *lazy* for a labelling of the basis: its
entry at `(a, b)` depends on the hidden values only through their coordinates in the labels of `a`
and `b`. -/
def Lazy {α : Type*} (lab : α → Finset S) (ρ : ((s : S) → D s) → Matrix α α ℂ) : Prop :=
  ∀ a b v v', Agree (lab a ∪ lab b) v v' → ρ v a b = ρ v' a b

/-- An operator is supported on the basis states whose label contains `T`. -/
def SuppAt {α : Type*} (lab : α → Finset S) (T : Finset S) (σ : Matrix α α ℂ) : Prop :=
  ∀ a b, σ a b ≠ 0 → T ⊆ lab a ∧ T ⊆ lab b

/-- A family of maps indexed by the hidden values preserves laziness on families supported on the
labels containing `T`. -/
def LazyMap {α β : Type*} (labA : α → Finset S) (labB : β → Finset S) (T : Finset S)
    (Φ : ((s : S) → D s) → MatrixMap α β) : Prop :=
  ∀ ρ : ((s : S) → D s) → Matrix α α ℂ, Lazy labA ρ → (∀ v, SuppAt labA T (ρ v)) →
    Lazy labB fun v ↦ Φ v (ρ v)

theorem lazyMap_congr {α β : Type*} {labA : α → Finset S} {labB : β → Finset S} {T : Finset S}
    {Φ Ψ : ((s : S) → D s) → MatrixMap α β} (h : ∀ v, Φ v = Ψ v)
    (hΨ : LazyMap labA labB T Ψ) : LazyMap labA labB T Φ := by
  rwa [show Φ = Ψ from funext h]

omit [DecidableEq S] in
/-- Every operator is supported above the empty set. -/
theorem suppAt_empty {α : Type*} (lab : α → Finset S) (σ : Matrix α α ℂ) : SuppAt lab ∅ σ :=
  fun _ _ _ ↦ ⟨Finset.empty_subset _, Finset.empty_subset _⟩

/-- A family that does not depend on the hidden values is lazy. -/
theorem lazy_const {α : Type*} (lab : α → Finset S) (ρ : Matrix α α ℂ) :
    Lazy (D := D) lab fun _ ↦ ρ :=
  fun _ _ _ _ _ ↦ rfl

/-- Relabelling along a bijection that preserves the labels preserves laziness. -/
theorem lazy_relabel {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {labA : α → Finset S} {labB : β → Finset S} (e : α ≃ β) (he : ∀ a, labB (e a) = labA a)
    {ρ : ((s : S) → D s) → Matrix α α ℂ} (hρ : Lazy labA ρ) :
    Lazy labB fun v ↦ (SubInstrument.relabel e).branch () (ρ v) := by
  intro a b v v' h
  simp only [SubInstrument.relabel_branch_apply, submatrix_apply]
  refine hρ _ _ v v' ?_
  rwa [← he (e.symm a), ← he (e.symm b), e.apply_symm_apply, e.apply_symm_apply]

/-- A map on the left factor, the labels on the right factor: laziness is preserved. -/
theorem lazy_amplify {α β R : Type*} (Φ : MatrixMap α β) {lab : R → Finset S}
    {ρ : ((s : S) → D s) → Matrix (α × R) (α × R) ℂ} (hρ : Lazy (fun p ↦ lab p.2) ρ) :
    Lazy (fun p : β × R ↦ lab p.2) fun v ↦ Φ.amplify R (ρ v) := by
  intro a b v v' h
  simp only [MatrixMap.amplify_apply]
  have hb : (ρ v).submatrix (·, a.2) (·, b.2) = (ρ v').submatrix (·, a.2) (·, b.2) := by
    ext x y
    exact hρ (x, a.2) (y, b.2) v v' h
  rw [hb]

/-- A lazy family of maps framed by an ancilla on the right is lazy. -/
theorem lazyMap_amplify {α β : Type*} {labA : α → Finset S} {labB : β → Finset S}
    {T : Finset S} {Φ : ((s : S) → D s) → MatrixMap α β} (hΦ : LazyMap labA labB T Φ)
    (E : Type*) :
    LazyMap (fun p : α × E ↦ labA p.1) (fun p : β × E ↦ labB p.1) T
      fun v ↦ (Φ v).amplify E := by
  intro ρ hρ hs a b v v' h
  simp only [MatrixMap.amplify_apply]
  exact hΦ (fun v ↦ (ρ v).submatrix (·, a.2) (·, b.2))
    (fun x y u u' hu ↦ hρ (x, a.2) (y, b.2) u u' hu)
    (fun u x y hxy ↦ hs u (x, a.2) (y, b.2) hxy) a.1 b.1 v v' h

/-- The partial trace over an unlabelled factor preserves laziness. -/
theorem lazy_traceRight {α E : Type*} [Fintype E] {lab : α → Finset S}
    {ρ : ((s : S) → D s) → Matrix (α × E) (α × E) ℂ} (hρ : Lazy (fun p ↦ lab p.1) ρ) :
    Lazy lab fun v ↦ MatrixMap.traceRight α E (ρ v) := by
  intro a b v v' h
  simp only [MatrixMap.traceRight_apply]
  exact Finset.sum_congr rfl fun r _ ↦ hρ (a, r) (b, r) v v' h

omit [DecidableEq S] in
/-- The partial trace over an unlabelled factor preserves supports. -/
theorem suppAt_traceRight {α E : Type*} [Fintype E] {lab : α → Finset S} {T : Finset S}
    {σ : Matrix (α × E) (α × E) ℂ} (h : SuppAt (fun p ↦ lab p.1) T σ) :
    SuppAt lab T (MatrixMap.traceRight α E σ) := by
  intro a b hab
  rw [MatrixMap.traceRight_apply] at hab
  obtain ⟨r, -, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  exact h (a, r) (b, r) hr

/-- **Kraus maps that never lower the label.** If every nonzero entry `K v b a` of the Kraus
operators has `lab a ⊆ lab b`, and the entries at inputs `a` labelled above `T` depend on the
hidden values only through the coordinates in the output label, the Kraus maps preserve laziness
on families supported above `T`. -/
theorem lazyMap_conj {α β : Type*} [Fintype α] {labA : α → Finset S} {labB : β → Finset S}
    {T : Finset S} (K : ((s : S) → D s) → Matrix β α ℂ)
    (hmono : ∀ v b a, K v b a ≠ 0 → labA a ⊆ labB b)
    (hK : ∀ v v' b a, T ⊆ labA a → Agree (labB b) v v' → K v b a = K v' b a) :
    LazyMap labA labB T fun v ↦ MatrixMap.conj (K v) := by
  intro ρ hρ hs b b' v v' h
  simp only [MatrixMap.conj_apply, Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a' _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases h1 : K v b a = 0 ∧ K v' b a = 0
  · simp [h1.1, h1.2]
  by_cases h2 : K v b' a' = 0 ∧ K v' b' a' = 0
  · simp [h2.1, h2.2]
  have ha : labA a ⊆ labB b := by
    rcases not_and_or.mp h1 with h1 | h1
    · exact hmono v b a h1
    · exact hmono v' b a h1
  have ha' : labA a' ⊆ labB b' := by
    rcases not_and_or.mp h2 with h2 | h2
    · exact hmono v b' a' h2
    · exact hmono v' b' a' h2
  have hρe : ρ v a a' = ρ v' a a' := hρ a a' v v' (h.mono (Finset.union_subset_union ha ha'))
  by_cases h3 : ρ v a a' = 0
  · rw [← hρe, h3]
    simp
  obtain ⟨hT, hT'⟩ := hs v a a' h3
  rw [hρe, hK v v' b a hT (h.mono Finset.subset_union_left),
    hK v v' b' a' hT' (h.mono Finset.subset_union_right)]

/-- The diagonal mass of a set of states with one label `T` reads only the entries labelled
inside `T`. -/
theorem diagMass_eq_of_label {α : Type} [Fintype α] (lab : α → Finset S) (T : Finset S)
    (C : Set α) (hC : ∀ a ∈ C, lab a = T) {σ σ' : Matrix α α ℂ}
    (h : ∀ p q, lab p ∪ lab q ⊆ T → σ p q = σ' p q) : diagMass C σ = diagMass C σ' := by
  unfold diagMass
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases ha : a ∈ C
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha,
      h a a (by rw [hC a ha, Finset.union_self])]
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]

/-- The diagonal mass of the empty set vanishes. -/
theorem diagMass_empty {α : Type} [Fintype α] (σ : Matrix α α ℂ) :
    diagMass (∅ : Set α) σ = 0 := by
  simp [diagMass]

omit [DecidableEq S] in
/-- The diagonal mass of a set of states labelled `T` vanishes on an operator supported above a
set `T'` not contained in `T`. -/
theorem diagMass_eq_zero_of_suppAt {α : Type} [Fintype α] (lab : α → Finset S) (T T' : Finset S)
    (C : Set α) (hC : ∀ a ∈ C, lab a = T) (hT : ¬ T' ⊆ T) {σ : Matrix α α ℂ}
    (hσ : SuppAt lab T' σ) : diagMass C σ = 0 := by
  unfold diagMass
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  by_cases ha : a ∈ C
  · rw [Set.indicator_of_mem ha]
    by_cases h0 : σ a a = 0
    · simp [h0]
    · exact absurd (hC a ha ▸ (hσ a a h0).1) hT
  · exact Set.indicator_of_notMem ha _

end lazy

/-! ## The view of a runtime that is lazy in a classical label -/

section core

variable {S : Type} [DecidableEq S] {D : S → Type}
  {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {Ω : QReg → Type w} {Dr : QReg} (init : SubState Dr)
  (step : ((s : S) → D s) → ∀ i, SubInstrument (spec.In i × Dr) (spec.Out i × Dr) (spec.Result i))
  (lab : Dr → Finset S) (need : spec.Port → Finset S)

/-- The runtime of a family of steps on one register, at the hidden values `v`. -/
@[reducible]
noncomputable def famRuntime (v : (s : S) → D s) : QuantumRuntime spec where
  D := Dr
  init := init
  step := step v

/-- The steps are lazy in the label of the register: every branch of port `i` preserves laziness
on families supported on the register states labelled above `need i`. -/
def StepLazy : Prop :=
  ∀ i r, LazyMap (fun p : spec.In i × Dr ↦ lab p.2) (fun p : spec.Out i × Dr ↦ lab p.2) (need i)
    fun v ↦ (step v i).branch r

/-- The operator presented to a call of port `i` is supported on the register states labelled above
`need i`. -/
def CallSupp : ∀ (i : spec.Port) (E : QReg),
    Matrix ((spec.In i × Dr) × E) ((spec.In i × Dr) × E) ℂ → Prop :=
  fun i _ σ ↦ SuppAt (fun p ↦ lab p.1.2) (need i) σ

variable {init step lab need}

/-- A call of a lazy runtime on a lazy family, presented operators supported above `need i`, is
lazy. -/
theorem lazy_queryStep (hstep : StepLazy step lab need) (i : spec.Port) (E : QReg) {A : QReg}
    (ℓ : A ≃ spec.In i × E) (r : spec.Result i) {ρ : ((s : S) → D s) → Matrix (A × Dr) (A × Dr) ℂ}
    (hρ : Lazy (fun p ↦ lab p.2) ρ)
    (hs : ∀ v, CallSupp lab need i E
      ((SubInstrument.relabel (queryEquivIn ℓ Dr)).branch () (ρ v))) :
    Lazy (fun p : (spec.Out i × E) × Dr ↦ lab p.2)
      fun v ↦ ((famRuntime init step v).queryStep i E ℓ).branch r (ρ v) := by
  have h : ∀ v, ((famRuntime init step v).queryStep i E ℓ).branch r (ρ v) =
      (SubInstrument.relabel (queryEquivOut (spec.Out i) Dr E)).branch ()
        (((step v i).branch r).amplify E
          ((SubInstrument.relabel (queryEquivIn ℓ Dr)).branch () (ρ v))) :=
    fun v ↦ queryStep_branch_apply (R := famRuntime init step v) i E ℓ r (ρ v)
  simp only [h]
  exact lazy_relabel (labA := fun p : (spec.Out i × Dr) × E ↦ lab p.1.2) _ (fun _ ↦ rfl)
    (lazyMap_amplify (hstep i r) E _
      (lazy_relabel (labA := fun p : A × Dr ↦ lab p.2) _ (fun _ ↦ rfl) hρ) hs)

/-- **The view of a lazy runtime.** Let a family of runtimes on one register be lazy in a label of
the register (`StepLazy`): port `i` acts on the states labelled above `need i` with entries
depending on the hidden values only through the coordinates of the label of the output, and never
lowers the label. If the initial states are lazy and every call of the run of the template `y`
receives an operator supported above `need i`, the `j`-th call weights agree for hidden values
agreeing on `T`, for weights that read only the entries labelled inside `T`. -/
theorem queryWeight_eq_of_lazy (hstep : StepLazy step lab need)
    (wt : ((s : S) → D s) → ∀ i, Matrix (spec.In i × Dr) (spec.In i × Dr) ℂ → ℝ≥0∞)
    (T : Finset S)
    (hw : ∀ v v' i (σ σ' : Matrix (spec.In i × Dr) (spec.In i × Dr) ℂ), Agree T v v' →
      SuppAt (fun p ↦ lab p.2) (need i) σ → SuppAt (fun p ↦ lab p.2) (need i) σ' →
      (∀ p q, lab p.2 ∪ lab q.2 ⊆ T → σ p q = σ' p q) → wt v i σ = wt v' i σ')
    {A : QReg} (y : QuantumComp L spec Ω A) (ρ : ((s : S) → D s) → Matrix (A × Dr) (A × Dr) ℂ)
    (hρ : Lazy (fun p ↦ lab p.2) ρ)
    (hsupp : ∀ v, (famRuntime init step v).ForallQueries I (CallSupp lab need) y (ρ v)) (j : ℕ)
    {v v' : (s : S) → D s} (hv : Agree T v v') :
    (famRuntime init step v).queryWeight I (wt v) y (ρ v) j =
      (famRuntime init step v').queryWeight I (wt v') y (ρ v') j := by
  induction y using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    simp only [queryWeight_primBind]
    exact tsum_congr fun b ↦ ih b _ (lazy_amplify _ hρ)
      (fun u ↦ (forallQueries_primBind_iff I o k _).mp (hsupp u) b) j
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero =>
      simp only [queryWeight_queryBind_zero]
      have hl : Lazy (fun p : spec.In i × Dr ↦ lab p.2) fun u ↦ callInput ℓ Dr (ρ u) :=
        lazy_traceRight (lazy_relabel _ (fun _ ↦ rfl) hρ)
      refine hw v v' i _ _ hv (suppAt_traceRight ((forallQueries_queryBind_iff I i E ℓ k _).mp
        (hsupp v)).1) (suppAt_traceRight ((forallQueries_queryBind_iff I i E ℓ k _).mp
        (hsupp v')).1) fun p q hpq ↦ hl p q v v' (hv.mono hpq)
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      exact tsum_congr fun r ↦ ih r _
        (lazy_queryStep hstep i E ℓ r hρ
          fun u ↦ ((forallQueries_queryBind_iff I i E ℓ k _).mp (hsupp u)).1)
        (fun u ↦ ((forallQueries_queryBind_iff I i E ℓ k _).mp (hsupp u)).2 r) j

/-- **The view of a lazy runtime, diagonal masses.** The diagonal masses of sets of states labelled
`T` at the `j`-th call agree for hidden values agreeing on `T`. -/
theorem queryWeight_diagMass_eq_of_lazy (hstep : StepLazy step lab need) (T : Finset S)
    (C : ∀ i, Set (spec.In i × Dr)) (hC : ∀ i p, p ∈ C i → lab p.2 = T)
    {A : QReg} (y : QuantumComp L spec Ω A) (ρ : ((s : S) → D s) → Matrix (A × Dr) (A × Dr) ℂ)
    (hρ : Lazy (fun p ↦ lab p.2) ρ)
    (hsupp : ∀ v, (famRuntime init step v).ForallQueries I (CallSupp lab need) y (ρ v)) (j : ℕ)
    {v v' : (s : S) → D s} (hv : Agree T v v') :
    (famRuntime init step v).queryWeight I (fun i ↦ diagMass (C i)) y (ρ v) j =
      (famRuntime init step v').queryWeight I (fun i ↦ diagMass (C i)) y (ρ v') j :=
  queryWeight_eq_of_lazy I hstep (fun _ i ↦ diagMass (C i)) T
    (fun _ _ i _ _ _ _ _ h ↦ diagMass_eq_of_label (fun p : spec.In i × Dr ↦ lab p.2) T (C i)
      (hC i) h) y ρ hρ hsupp j hv

end core

section viewOn

variable {S : Type} {D : S → Type} {spec : QuantumOracleSpec.{u₁, v₁}}
  (R : QuantumRuntime spec) {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w}

/-- A predicate that holds of every operator holds of the operators presented to every call. -/
theorem forallQueries_of_forall
    {P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    (hP : ∀ i E σ, P i E σ) {A : QReg} (x : QuantumComp L spec Ω A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) : R.ForallQueries I P x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind _ o k ih => exact (forallQueries_primBind_iff I o k ρ).mpr fun b ↦ ih b _
  | queryBind _ i E ℓ k ih =>
    exact (forallQueries_queryBind_iff I i E ℓ k ρ).mpr ⟨hP _ _ _, fun r ↦ ih r _⟩

/-- **The lazy-sampling property on some ports**: `ViewBy` for the weights that vanish on the ports
outside `P`. -/
def ViewByOn {A : QReg} (P : spec.Port → Prop) (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) : Prop :=
  ∀ (T : Finset S) (v v' : (s : S) → D s), Agree T v v' →
    ∀ C : ∀ i, Set (spec.In i × R.D), (∀ i p, p ∈ C i → lab p.2 = T) → (∀ i, ¬ P i → C i = ∅) →
      R.queryWeight I (fun i ↦ diagMass (C i)) (x v) (ρ v) j =
        R.queryWeight I (fun i ↦ diagMass (C i)) (x v') (ρ v') j

variable {R I}

/-- The lazy-sampling property gives it on every set of ports. -/
theorem ViewBy.viewByOn {A : QReg} {lab : R.D → Finset S}
    {x : ((s : S) → D s) → QuantumComp L spec Ω A}
    {ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ} {j : ℕ} (h : ViewBy R I lab x ρ j)
    (P : spec.Port → Prop) : ViewByOn R I P lab x ρ j :=
  fun T v v' hv C hC _ ↦ h T v v' hv C hC

end viewOn

/-! ## Template programs of runtime 2 -/

section templates

variable (X Z : Type)

/-- A template program port of runtime 2: hardwire a cell of `h`, `k` or `k'` to a value, both
functions of the hidden values restricted to the coordinates `T`. -/
inductive LazyProg (S : Type) (D : S → Type) where
  /-- Hardwire the cell `(c v|_T).1` of `h` to `(c v|_T).2`. -/
  | programH (T : Finset S) (c : ((s : {s // s ∈ T}) → D s.1) → Z × X)
  /-- Hardwire the cell `(c v|_T).1` of `k` to `(c v|_T).2`. -/
  | programK (T : Finset S) (c : ((s : {s // s ∈ T}) → D s.1) → X × Z)
  /-- Hardwire the cell `(c v|_T).1` of `k'` to `(c v|_T).2`. -/
  | programK' (T : Finset S) (c : ((s : {s // s ∈ T}) → D s.1) → X × Z)

end templates

/-- The restriction of the hidden values to the coordinates `T`. -/
def restrictTo {S : Type} {D : S → Type} (T : Finset S) (v : (s : S) → D s) :
    (s : {s // s ∈ T}) → D s.1 :=
  fun s ↦ v s.1

theorem restrictTo_eq {S : Type} {D : S → Type} {T : Finset S} {v v' : (s : S) → D s}
    (h : Agree T v v') : restrictTo T v = restrictTo T v' :=
  funext fun s ↦ h s.1 s.2

namespace LazyProg

open Quantum.Sponge

variable {X Z S : Type} {D : S → Type}

/-- The coordinates the port's cell and value depend on. -/
def need : LazyProg X Z S D → Finset S
  | programH T _ => T
  | programK T _ => T
  | programK' T _ => T

/-- The classical result of a template program port: that of the program port it realizes. -/
@[reducible]
def Result : LazyProg X Z S D → Type
  | programH .. => Option X × Option X
  | programK .. => Option Z × Option Z
  | programK' .. => Option Z × Option Z

/-- The program port of runtime 2 that a template program port realizes at the hidden values
`v`. -/
def realize (v : (s : S) → D s) : LazyProg X Z S D → HwProg X Z
  | programH T c => .programH (c (restrictTo T v)).1 (c (restrictTo T v)).2
  | programK T c => .programK (c (restrictTo T v)).1 (c (restrictTo T v)).2
  | programK' T c => .programK' (c (restrictTo T v)).1 (c (restrictTo T v)).2

/-- A template program port realizes the same port at hidden values agreeing on its coordinates. -/
theorem realize_eq (p : LazyProg X Z S D) {v v' : (s : S) → D s} (h : Agree p.need v v') :
    p.realize v = p.realize v' := by
  cases p <;> simp only [realize, need] at h ⊢ <;> rw [restrictTo_eq h]

end LazyProg

section runtime2

open Quantum.Sponge

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M] {S : Type} [DecidableEq S] {D : S → Type}

/-- Hardwiring a cell: the hardwired cells after the program port `c`. -/
def progUpdate : HwProg X Z → Hw X Z → Hw X Z
  | .programH z x, W => (Function.update W.1 z (some x), W.2)
  | .programK x w, W => (W.1, Function.update W.2.1 x (some w), W.2.2)
  | .programK' x w, W => (W.1, W.2.1, Function.update W.2.2 x (some w))

/-- The memory updates of a read port never lower the label. -/
def ReadMono (lab : Hw X Z × M → Finset S) : HwRead X Z M → Prop
  | .readH _ upd => ∀ W m o, lab (W, m) ⊆ lab (W, upd m o)
  | .readK _ upd => ∀ W m o, lab (W, m) ⊆ lab (W, upd m o)
  | .readK' _ upd => ∀ W m o, lab (W, m) ⊆ lab (W, upd m o)

/-- A template program port is *self-disclosing* for the label `lab` if hardwiring its cell, at any
hidden values and from any classical data, records its coordinates in the label. -/
def SelfDisc (lab : Hw X Z × M → Finset S) (p : LazyProg X Z S D) : Prop :=
  ∀ (v : (s : S) → D s) (b : Hw X Z × M), p.need ⊆ lab (progUpdate (p.realize v) b.1, b.2)

variable (X Z M) in
/-- **The template signature of runtime 2**: the sponge ports, the read ports whose memory update
never lowers the label `lab`, and the template program ports satisfying `good`. -/
@[reducible]
def lazySpec (lab : Hw X Z × M → Finset S) (D : S → Type) (good : LazyProg X Z S D → Prop) :
    QuantumOracleSpec.{0, 0} where
  Port := (SpongePort ⊕ {c : HwRead X Z M // ReadMono lab c}) ⊕ {p : LazyProg X Z S D // good p}
  In
    | .inl (.inl i) => (hwSpec X Z M).In (.inl (.inl i))
    | .inl (.inr c) => (hwSpec X Z M).In (.inl (.inr c.1))
    | .inr _ => QReg.of Unit
  Out
    | .inl (.inl i) => (hwSpec X Z M).Out (.inl (.inl i))
    | .inl (.inr c) => (hwSpec X Z M).Out (.inl (.inr c.1))
    | .inr _ => QReg.of Unit
  Result
    | .inl (.inl i) => (hwSpec X Z M).Result (.inl (.inl i))
    | .inl (.inr c) => (hwSpec X Z M).Result (.inl (.inr c.1))
    | .inr p => p.1.Result

variable {lab : Hw X Z × M → Finset S} {good : LazyProg X Z S D → Prop}

variable (lab good) in
/-- The coordinates a template port needs disclosed before it is called: none for the sponge and
read ports, those of its cell and value for a program port. -/
def lazyNeed : (lazySpec X Z M lab D good).Port → Finset S
  | .inl _ => ∅
  | .inr p => p.1.need

/-- The realization of a template program at the hidden values `v`, as a lens: the sponge and read
ports stay, a template program port becomes the program port it realizes. -/
def realizeLens {L : LocalSig.{u, v}} (v : (s : S) → D s) :
    IPFunctor.Lens (QuantumComp.toIPFunctor L (lazySpec X Z M lab D good))
      (QuantumComp.toIPFunctor L (hwSpec X Z M)) where
  toFunA _
    | .prim o => .prim o
    | .query (.inl (.inl i)) E ℓ => .query (.inl (.inl i)) E ℓ
    | .query (.inl (.inr c)) E ℓ => .query (.inl (.inr c.1)) E ℓ
    | .query (.inr p) E ℓ => .query (.inr (p.1.realize v)) E ℓ
  toFunB _ c := by
    rcases c with o | ⟨(i | c) | ⟨p, hp⟩, E, ℓ⟩
    · exact id
    · exact id
    · exact id
    · cases p <;> exact id
  src_eq _ c _ := by
    rcases c with o | ⟨(i | c) | ⟨p, hp⟩, E, ℓ⟩
    · rfl
    · rfl
    · rfl
    · cases p <;> rfl

/-- **The program family of a template**: at the hidden values `v`, every template program port
calls the program port it realizes. -/
def realize {L : LocalSig.{u, v}} {Ω : QReg → Type w} {A : QReg} (v : (s : S) → D s)
    (y : QuantumComp L (lazySpec X Z M lab D good) Ω A) : QuantumComp L (hwSpec X Z M) Ω A :=
  IPFunctor.IFreeM.mapLens (realizeLens v) y

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]

/-- The steps of the template runtime at the hidden values `v`: those of runtime 2 at the realized
ports. -/
noncomputable def lazyStep (m₀ : M) (v : (s : S) → D s) :
    ∀ i : (lazySpec X Z M lab D good).Port,
      SubInstrument ((lazySpec X Z M lab D good).In i × QReg.of (HwReg X Z M))
        ((lazySpec X Z M lab D good).Out i × QReg.of (HwReg X Z M))
        ((lazySpec X Z M lab D good).Result i)
  | .inl (.inl i) => (runtime2 X Z m₀).step (.inl (.inl i))
  | .inl (.inr c) => (runtime2 X Z m₀).step (.inl (.inr c.1))
  | .inr ⟨.programH T c, _⟩ => (runtime2 X Z m₀).step (.inr ((LazyProg.programH T c).realize v))
  | .inr ⟨.programK T c, _⟩ => (runtime2 X Z m₀).step (.inr ((LazyProg.programK T c).realize v))
  | .inr ⟨.programK' T c, _⟩ =>
      (runtime2 X Z m₀).step (.inr ((LazyProg.programK' T c).realize v))

/-- A weight of runtime 2 read on the template ports at the hidden values `v`. -/
def realizeWeight (v : (s : S) → D s)
    (wt : ∀ i, Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞) :
    ∀ i : (lazySpec X Z M lab D good).Port,
      Matrix ((lazySpec X Z M lab D good).In i × QReg.of (HwReg X Z M))
        ((lazySpec X Z M lab D good).In i × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞
  | .inl (.inl i) => wt (.inl (.inl i))
  | .inl (.inr c) => wt (.inl (.inr c.1))
  | .inr p => wt (.inr (p.1.realize v))

omit [DecidableEq S] in
/-- **Running the realized program.** The weights of runtime 2 running the realization of a
template at `v` are those of the template runtime at `v` running the template. -/
theorem queryWeight_realize {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} (m₀ : M)
    (v : (s : S) → D s)
    (wt : ∀ i, Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞)
    {A : QReg} (y : QuantumComp L (lazySpec X Z M lab D good) Ω A)
    (ρ : Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ) (j : ℕ) :
    (runtime2 X Z m₀).queryWeight I wt (realize v y) ρ j =
      (famRuntime (initHw X Z m₀) (lazyStep m₀) v).queryWeight I (realizeWeight v wt) y ρ j := by
  induction y using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rfl
  | primBind _ o k ih => exact tsum_congr fun b ↦ ih b _ j
  | queryBind _ i E ℓ k ih =>
    rcases i with (i | c) | ⟨p, hp⟩
    · cases j with
      | zero => rfl
      | succ j => exact tsum_congr fun r ↦ ih r _ j
    · cases j with
      | zero => rfl
      | succ j => exact tsum_congr fun r ↦ ih r _ j
    · cases p <;> cases j <;> first | rfl | exact tsum_congr fun r ↦ ih r _ _

theorem clsKraus_ne_zero_cls {T B : Type} [DecidableEq B] {p : B → Prop} [DecidablePred p]
    {φ : B → B} {R : B → Matrix T T ℂ} {s s' : T × B} (h : clsKraus p φ R s' s ≠ 0) :
    p s.2 ∧ s'.2 = φ s.2 := by
  rw [clsKraus_apply] at h
  split_ifs at h with hb
  · exact hb
  · exact absurd rfl h

omit [Nonempty X] [Nonempty Z] in
/-- The sponge ports act block by block on the classical data. -/
theorem spongeHardwired_U_ne_zero_snd (W₀ : Hw X Z) (m₀ : M) (i : SpongePort)
    {a a' : spongeIn X Z i} {s s' : HwReg X Z M}
    (h : (spongeHardwired X Z W₀ m₀).U i (a', s') (a, s) ≠ 0) : s'.2 = s.2 := by
  rw [spongeHardwired_U] at h
  obtain ⟨D', b'⟩ := s'
  obtain ⟨D, b⟩ := s
  simp only [liftBlocks, submatrix_apply, hwSplit, Equiv.prodAssoc_symm_apply,
    blockDiagonal_apply] at h
  split_ifs at h with hb
  · exact hb
  · exact absurd rfl h

omit [Fintype M] [DecidableEq S] [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- A read port moves the memory `m` to `upd m o`. -/
theorem hwReadKraus_ne_zero_label (c : HwRead X Z M) (hc : ReadMono lab c) (r : c.Result)
    {u u' : Unit} {s s' : HwReg X Z M} (h : hwReadKraus c r (u', s') (u, s) ≠ 0) :
    lab s.2 ⊆ lab s'.2 := by
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ, ← hp]
    exact hc s.2.1 s.2.2 r.1
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ, ← hp]
    exact hc s.2.1 s.2.2 r.1
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ, ← hp]
    exact hc s.2.1 s.2.2 r.1

omit [Fintype M] [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- A program port hardwires its cell. -/
theorem hwProgKraus_ne_zero_snd (c : HwProg X Z) (r : c.Result) {u u' : Unit}
    {s s' : HwReg X Z M} (h : hwProgKraus c r (u', s') (u, s) ≠ 0) :
    s'.2 = (progUpdate c s.2.1, s.2.2) := by
  cases c with
  | programH z x =>
    simp only [hwProgKraus, programKrausH] at h
    exact (clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2).2
  | programK x w =>
    simp only [hwProgKraus, programKrausK] at h
    exact (clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2).2
  | programK' x w =>
    simp only [hwProgKraus, programKrausK'] at h
    exact (clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2).2

/-- **Runtime 2 is lazy in the label of its classical data.** Let hardwiring a cell never lower
the label, and let a template program port, called on states labelled above `nd` of it, record its
coordinates in the label when it hardwires its cell. Then the template runtime is lazy
(`StepLazy`) for the needs `nd`: the sponge ports act block by block on the classical data, the
read ports never lower the label (`ReadMono`), and a template program port realizes, on the states
its output is labelled with, a port that depends on the hidden values only through the coordinates
of that label. -/
theorem stepLazy_lazyStep (m₀ : M) (hlab : ∀ (c : HwProg X Z) (b : Hw X Z × M),
      lab b ⊆ lab (progUpdate c b.1, b.2))
    (nd : (lazySpec X Z M lab D good).Port → Finset S)
    (hprog : ∀ p (hp : good p) (v : (s : S) → D s) (b : Hw X Z × M), nd (.inr ⟨p, hp⟩) ⊆ lab b →
      p.need ⊆ lab (progUpdate (p.realize v) b.1, b.2)) :
    StepLazy (lazyStep (lab := lab) (D := D) (good := good) m₀)
      (fun r : QReg.of (HwReg X Z M) ↦ lab r.2) nd := by
  intro i r
  rcases i with (i | ⟨c, hc⟩) | ⟨p, hp⟩
  · refine lazyMap_congr (fun _ ↦ runtime2_branch (X := X) (Z := Z) m₀ (.inl (.inl i)) r)
      (lazyMap_conj _ (fun _ b a hK ↦ ?_) fun _ _ _ _ _ _ ↦ rfl)
    obtain ⟨a, s⟩ := a
    obtain ⟨a', s'⟩ := b
    show lab s.2 ⊆ lab s'.2
    rw [spongeHardwired_U_ne_zero_snd (hwEmpty X Z) m₀ i hK]
  · refine lazyMap_congr (fun _ ↦ runtime2_branch (X := X) (Z := Z) m₀ (.inl (.inr c)) r)
      (lazyMap_conj _ (fun _ b a hK ↦ ?_) fun _ _ _ _ _ _ ↦ rfl)
    obtain ⟨a, s⟩ := a
    obtain ⟨a', s'⟩ := b
    exact hwReadKraus_ne_zero_label c hc r hK
  · have hmono : ∀ (c : HwProg X Z) (r : c.Result) (b a : Unit × HwReg X Z M),
        hwProgKraus c r b a ≠ 0 → lab a.2.2 ⊆ lab b.2.2 := by
      rintro c r ⟨u', s'⟩ ⟨u, s⟩ hK
      rw [hwProgKraus_ne_zero_snd c r hK]
      exact hlab c s.2
    have hneed : ∀ (u : (s : S) → D s) (r : (p.realize u).Result) (b a : Unit × HwReg X Z M),
        nd (.inr ⟨p, hp⟩) ⊆ lab a.2.2 → hwProgKraus (p.realize u) r b a ≠ 0 →
          p.need ⊆ lab b.2.2 := by
      rintro u r ⟨u', s'⟩ ⟨u, s⟩ hT hK
      rw [hwProgKraus_ne_zero_snd _ r hK]
      exact hprog p hp _ s.2 hT
    cases p with
    | programH T c =>
      refine lazyMap_congr (fun v ↦ runtime2_branch (X := X) (Z := Z) m₀
        (.inr ((LazyProg.programH T c).realize v)) r) (lazyMap_conj _
          (fun v b a hK ↦ hmono ((LazyProg.programH T c).realize v) r b a hK)
          fun v v' b a hT hv ↦ ?_)
      by_cases hTb : T ⊆ lab b.2.2
      · exact congrArg (fun u ↦ hwProgKraus (.programH (c u).1 (c u).2) r b a)
          (restrictTo_eq (hv.mono hTb))
      · have h0 : ∀ u, hwProgKraus ((LazyProg.programH T c).realize u) r b a = 0 := fun u ↦ by
          by_contra hne
          exact hTb (hneed u r b a hT hne)
        exact (h0 v).trans (h0 v').symm
    | programK T c =>
      refine lazyMap_congr (fun v ↦ runtime2_branch (X := X) (Z := Z) m₀
        (.inr ((LazyProg.programK T c).realize v)) r) (lazyMap_conj _
          (fun v b a hK ↦ hmono ((LazyProg.programK T c).realize v) r b a hK)
          fun v v' b a hT hv ↦ ?_)
      by_cases hTb : T ⊆ lab b.2.2
      · exact congrArg (fun u ↦ hwProgKraus (.programK (c u).1 (c u).2) r b a)
          (restrictTo_eq (hv.mono hTb))
      · have h0 : ∀ u, hwProgKraus ((LazyProg.programK T c).realize u) r b a = 0 := fun u ↦ by
          by_contra hne
          exact hTb (hneed u r b a hT hne)
        exact (h0 v).trans (h0 v').symm
    | programK' T c =>
      refine lazyMap_congr (fun v ↦ runtime2_branch (X := X) (Z := Z) m₀
        (.inr ((LazyProg.programK' T c).realize v)) r) (lazyMap_conj _
          (fun v b a hK ↦ hmono ((LazyProg.programK' T c).realize v) r b a hK)
          fun v v' b a hT hv ↦ ?_)
      by_cases hTb : T ⊆ lab b.2.2
      · exact congrArg (fun u ↦ hwProgKraus (.programK' (c u).1 (c u).2) r b a)
          (restrictTo_eq (hv.mono hTb))
      · have h0 : ∀ u, hwProgKraus ((LazyProg.programK' T c).realize u) r b a = 0 := fun u ↦ by
          by_contra hne
          exact hTb (hneed u r b a hT hne)
        exact (h0 v).trans (h0 v').symm

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem diagMass_prog_congr (C : ∀ i, Set ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)))
    {c c' : HwProg X Z} (h : c = c') (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    diagMass (C (.inr c)) σ = diagMass (C (.inr c')) σ := by
  subst h
  rfl

/-- **The lazy-sampling property for runtime 2** (coordinates disclosed before programming). Let
the label `lab` of the classical data `(W, m)` (the disclosed coordinates recorded in the
hardwired cells and the memory) never drop when a cell is hardwired. Let `y` be a template
program: its program ports hardwire cells and values that are functions of the hidden values
restricted to coordinates `T`, and its read ports never lower the label. If the initial states are
lazy and every template program port is called on states whose label contains its `T` (the
coordinates are already disclosed), the realized programs satisfy the lazy-sampling property
`ViewBy` of runtime 2 at every call. -/
theorem viewBy_runtime2_realize {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w}
    (m₀ : M) (hlab : ∀ (c : HwProg X Z) (b : Hw X Z × M), lab b ⊆ lab (progUpdate c b.1, b.2))
    {A : QReg} (y : QuantumComp L (lazySpec X Z M lab D good) Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : Lazy (fun p ↦ lab p.2.2) ρ)
    (hsupp : ∀ v, (famRuntime (initHw X Z m₀) (lazyStep m₀) v).ForallQueries I
      (CallSupp (fun r : QReg.of (HwReg X Z M) ↦ lab r.2) (lazyNeed lab good)) y (ρ v))
    (j : ℕ) :
    ViewBy (runtime2 X Z m₀) I (fun r ↦ lab r.2) (fun v ↦ realize v y) ρ j := by
  intro T v v' hv C hC
  rw [queryWeight_realize, queryWeight_realize]
  refine queryWeight_eq_of_lazy I (stepLazy_lazyStep m₀ hlab (lazyNeed lab good)
      fun p _ _ b h ↦ h.trans (hlab _ b))
    (fun u ↦ realizeWeight u fun i ↦ diagMass (C i)) T (fun u u' i σ σ' hu hs hs' hσ ↦ ?_)
    y ρ hρ hsupp j hv
  rcases i with (i | c) | ⟨p, hp⟩
  · exact diagMass_eq_of_label (fun q ↦ lab q.2.2) T _ (fun q hq ↦ hC _ q hq) hσ
  · exact diagMass_eq_of_label (fun q ↦ lab q.2.2) T _ (fun q hq ↦ hC _ q hq) hσ
  · have hσ₁ : ∀ a b : Unit × HwReg X Z M, lab a.2.2 ∪ lab b.2.2 ⊆ T → σ a b = σ' a b := hσ
    have hs₁ : SuppAt (fun a : Unit × HwReg X Z M ↦ lab a.2.2) p.need σ := hs
    have hs₁' : SuppAt (fun a : Unit × HwReg X Z M ↦ lab a.2.2) p.need σ' := hs'
    have hC₁ : ∀ c, ∀ q ∈ C (.inr c), (fun a : Unit × HwReg X Z M ↦ lab a.2.2) q = T :=
      fun c q hq ↦ hC _ q hq
    show diagMass (C (.inr (p.realize u))) σ = diagMass (C (.inr (p.realize u'))) σ'
    by_cases hT : p.need ⊆ T
    · exact (diagMass_prog_congr C (p.realize_eq (hu.mono hT)) σ).trans
        (diagMass_eq_of_label (α := Unit × HwReg X Z M) _ T _ (hC₁ _) hσ₁)
    · exact (diagMass_eq_zero_of_suppAt (α := Unit × HwReg X Z M) _ T p.need _ (hC₁ _) hT
        hs₁).trans (diagMass_eq_zero_of_suppAt (α := Unit × HwReg X Z M) _ T p.need _ (hC₁ _) hT
          hs₁').symm

/-- **The lazy-sampling property for runtime 2, self-disclosing programming.** Let the label never
drop when a cell is hardwired, and let every template program port of `y` be self-disclosing
(`SelfDisc`: hardwiring its cell records its coordinates in the label). If the initial states are
lazy, the realized programs satisfy the lazy-sampling property at every call for the weights that
vanish on the program ports (`ViewByOn`); no condition on the run is needed. -/
theorem viewByOn_runtime2_realize {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w}
    (m₀ : M) (hlab : ∀ (c : HwProg X Z) (b : Hw X Z × M), lab b ⊆ lab (progUpdate c b.1, b.2))
    (hgood : ∀ p, good p → SelfDisc lab p)
    {A : QReg} (y : QuantumComp L (lazySpec X Z M lab D good) Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : Lazy (fun p ↦ lab p.2.2) ρ) (j : ℕ) :
    ViewByOn (runtime2 X Z m₀) I (fun i ↦ i.isLeft = true) (fun r ↦ lab r.2)
      (fun v ↦ realize v y) ρ j := by
  intro T v v' hv C hC hC0
  have hCe : ∀ c, C (.inr c) = ∅ := fun c ↦ hC0 _ (by simp)
  rw [queryWeight_realize, queryWeight_realize]
  refine queryWeight_eq_of_lazy I (stepLazy_lazyStep m₀ hlab (fun _ ↦ ∅)
      fun p hp v b _ ↦ hgood p hp v b)
    (fun u ↦ realizeWeight u fun i ↦ diagMass (C i)) T (fun u u' i σ σ' _ _ _ hσ ↦ ?_)
    y ρ hρ (fun u ↦ forallQueries_of_forall (famRuntime (initHw X Z m₀) (lazyStep m₀) u) I
      (fun _ _ σ ↦ suppAt_empty _ σ) y (ρ u)) j hv
  rcases i with (i | c) | ⟨p, hp⟩
  · exact diagMass_eq_of_label (fun q ↦ lab q.2.2) T _ (fun q hq ↦ hC _ q hq) hσ
  · exact diagMass_eq_of_label (fun q ↦ lab q.2.2) T _ (fun q hq ↦ hC _ q hq) hσ
  · show diagMass (C (.inr (p.realize u))) σ = diagMass (C (.inr (p.realize u'))) σ'
    rw [hCe, hCe]
    exact (diagMass_empty (α := Unit × HwReg X Z M) σ).trans (diagMass_empty σ').symm

end runtime2

end Quantum.Xmss.Hybrid

end
