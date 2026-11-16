module

public import Quantum.Xmss.Hybrid.Graded
public import Quantum.Xmss.Assembly.Reparam

@[expose] public section

/-!
# The hidden masses of the graded hybrid

The hidden sets of the graded hybrid (`sqrt_win_runtime1R_le_graded`) for runtime 1's table, and
the bounds on the hidden masses at the sponge ports (`spongeMass`) and the read ports (`readMass`)
of the canonical game against `runtimeR`, averaged over the honest table.

* **Hidden sets** (`pathH`, `pathK`, `pathK'`): the cells of the honest paths the template game
  programs (`pathProgs`, GameT's `progSet`), so `covers_of_progs` gives `Covers (tableHw L) …`
  for any further hidden sets added by union (the randomizer-base cells, kept generic).
* **Masses on reachable states** (`sum_totalWeight_portMass_runtimeR_le_inv`): Graded's
  `sum_totalWeight_portMass_runtimeR_le` asks every hidden cell that is not hardwired to name an
  undisclosed source in every register state. A cell of an honest path whose inputs are disclosed
  but whose slot is not yet programmed has no such source, so the condition is asked only on the
  states of an invariant `Inv` that the inputs of the calls of the ports `Q` satisfy
  (`ForallQueries` of `invSupp Q Inv`; for the template game: a disclosed input position has its
  slot's cells hardwired at every sponge and read call).
* **Averages** (`uavg_le_of_injOn`): the table with a pad, mapped injectively on a good set into
  public data and hidden values, the bad fraction paying the rest.
* **The bounds** (`uavg_totalWeight_portMass_le`, `uavg_spongeMass_le`, `uavg_readMass_le`): for the
  realized template game `realizeT (valueAt L) (gameT M upd (pubOf L) A)` with at most `N` calls of
  the ports, the averaged total hidden mass is at most `N (κ + bad)`, from a reparametrization,
  the game equation on the good set, the invariant, and per public datum the sources of the hidden
  cells (`Sources`, with the per-cell bound `κ`). `uavg_totalWeight_portMass_union_le` adds
  further hidden sets with their own bounds.
-/

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v u₁ v₁ w

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid

/-! ## Weights on the presented operators -/

section congr

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- **Only the presented operators matter for the weights**: two weights that agree on the
inputs of the calls satisfying `P` give the same weights to a program whose calls all satisfy
`P`. -/
theorem queryWeight_congr_of_forallQueries
    {P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    {w w' : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    (hw : ∀ i E σ, P i E σ →
      w i (MatrixMap.traceRight (spec.In i × R.D) E σ) =
        w' i (MatrixMap.traceRight (spec.In i × R.D) E σ))
    (x : QuantumComp L spec Ω A) (ρ : Matrix (A × R.D) (A × R.D) ℂ)
    (hx : R.ForallQueries I P x ρ) (j : ℕ) :
    R.queryWeight I w x ρ j = R.queryWeight I w' x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    simp only [queryWeight_primBind]
    exact tsum_congr fun b ↦ ih b _ (hx b) j
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero =>
      simp only [queryWeight_queryBind_zero]
      exact hw i E _ hx.1
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      exact tsum_congr fun r ↦ ih r _ (hx.2 r) j

/-- `queryWeight_congr_of_forallQueries` summed over the calls. -/
theorem totalWeight_congr_of_forallQueries
    {P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    {w w' : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    (hw : ∀ i E σ, P i E σ →
      w i (MatrixMap.traceRight (spec.In i × R.D) E σ) =
        w' i (MatrixMap.traceRight (spec.In i × R.D) E σ))
    (x : QuantumComp L spec Ω A) (ρ : Matrix (A × R.D) (A × R.D) ℂ)
    (hx : R.ForallQueries I P x ρ) :
    R.totalWeight I w x ρ = R.totalWeight I w' x ρ :=
  tsum_congr fun j ↦ queryWeight_congr_of_forallQueries R I hw x ρ hx j

/-- **Calls supported on an invariant**: at the ports `Q`, the presented operator has no diagonal
mass on the register states outside `Inv`. -/
def invSupp (Q : spec.Port → Prop) (Inv : R.D → Prop) :
    ∀ (i : spec.Port) (E : QReg), Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop :=
  fun i _ σ ↦ Q i → ∀ a, ¬Inv a.1.2 → σ a a = 0

end congr

/-! ## Diagonal masses on an invariant -/

section diag

/-- The mass of a set is that of its part in `T` when the diagonal vanishes outside `T`. -/
theorem diagMass_eq_inter {α : Type} [Fintype α] (S T : Set α) {σ : Matrix α α ℂ}
    (h : ∀ a, a ∉ T → σ a a = 0) : diagMass S σ = diagMass (S ∩ T) σ := by
  unfold diagMass
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases hS : a ∈ S <;> by_cases hT : a ∈ T <;> simp [hS, hT, h a]

/-- The diagonal of a partial trace vanishes where every diagonal block does. -/
theorem traceRight_diag_eq_zero {α E : Type} [Fintype E] {σ : Matrix (α × E) (α × E) ℂ} {a : α}
    (h : ∀ e, σ (a, e) (a, e) = 0) : MatrixMap.traceRight α E σ a a = 0 := by
  rw [MatrixMap.traceRight_apply]
  exact Finset.sum_eq_zero fun e _ ↦ h e

end diag

/-! ## The view lemma for `runtimeR` on an invariant -/

section runtimeR

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  {Sv : Type} [Fintype Sv] [DecidableEq Sv] {Dv : Sv → Type} [∀ s, Fintype (Dv s)]
  [∀ s, DecidableEq (Dv s)] [∀ s, Nonempty (Dv s)]
  {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w} {A : QReg}

variable (X Z S M' Sv Dv) in
/-- **The sources of the hidden cells** on the register states of an invariant `Inv`: every
hidden cell that is not hardwired in a state of `Inv` names sources, one of which is undisclosed
(`lab`) with its hidden value in a set `F` not depending on it; per cell the sets weigh at most
`κ`. As in `sum_totalWeight_portMass_runtimeR_le`, with the invariant. -/
structure Sources (lab : HwReg X Z (Finset S × M') → Finset Sv)
    (Inv : ((s : Sv) → Dv s) → HwReg X Z (Finset S × M') → Prop)
    (Hhv : ((s : Sv) → Dv s) → Set Z) (Hkv Hk'v : ((s : Sv) → Dv s) → Set X) (κ : ℝ≥0∞) where
  /-- The sources of an `h`-cell. -/
  sh : Z → HwReg X Z (Finset S × M') → Finset Sv
  /-- The sources of a `k`-cell. -/
  sk : X → HwReg X Z (Finset S × M') → Finset Sv
  /-- The sources of a `k'`-cell. -/
  sk' : X → HwReg X Z (Finset S × M') → Finset Sv
  /-- The values of a source that put the `h`-cell in the hidden set. -/
  Fh : Z → HwReg X Z (Finset S × M') → (s : Sv) → ((s : Sv) → Dv s) → Finset (Dv s)
  /-- The values of a source that put the `k`-cell in the hidden set. -/
  Fk : X → HwReg X Z (Finset S × M') → (s : Sv) → ((s : Sv) → Dv s) → Finset (Dv s)
  /-- The values of a source that put the `k'`-cell in the hidden set. -/
  Fk' : X → HwReg X Z (Finset S × M') → (s : Sv) → ((s : Sv) → Dv s) → Finset (Dv s)
  hFh : ∀ z r s v d, Fh z r s (Function.update v s d) = Fh z r s v
  hFk : ∀ y r s v d, Fk y r s (Function.update v s d) = Fk y r s v
  hFk' : ∀ y r s v d, Fk' y r s (Function.update v s d) = Fk' y r s v
  hh : ∀ v z r, Inv v r → z ∈ Hhv v → r.2.1.1 z = none →
    ∃ s ∈ sh z r, s ∉ lab r ∧ v s ∈ Fh z r s v
  hk : ∀ v y r, Inv v r → y ∈ Hkv v → r.2.1.2.1 y = none →
    ∃ s ∈ sk y r, s ∉ lab r ∧ v s ∈ Fk y r s v
  hk' : ∀ v y r, Inv v r → y ∈ Hk'v v → r.2.1.2.2 y = none →
    ∃ s ∈ sk' y r, s ∉ lab r ∧ v s ∈ Fk' y r s v
  hκh : ∀ z r v, ∑ s ∈ sh z r, ((Fh z r s v).card : ℝ≥0∞) * (Fintype.card (Dv s) : ℝ≥0∞)⁻¹ ≤ κ
  hκk : ∀ y r v, ∑ s ∈ sk y r, ((Fk y r s v).card : ℝ≥0∞) * (Fintype.card (Dv s) : ℝ≥0∞)⁻¹ ≤ κ
  hκk' : ∀ y r v, ∑ s ∈ sk' y r, ((Fk' y r s v).card : ℝ≥0∞) * (Fintype.card (Dv s) : ℝ≥0∞)⁻¹ ≤ κ

/-- The hidden sets of the ports `Q` on the states of `Inv`, empty elsewhere. -/
def invHidSet (Q : (recHwSpec X Z S M').Port → Prop) [DecidablePred Q]
    (Inv : HwReg X Z (Finset S × M') → Prop) (Hh : Set Z) (Hk Hk' : Set X)
    (i : (recHwSpec X Z S M').Port) :
    Set ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M'))) :=
  if Q i then extHidSet Hh Hk Hk' i ∩ {p | Inv p.2} else ∅

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- On the calls supported on the invariant, the hidden mass at the ports `Q` is that of the
states of the invariant. -/
theorem portMass_eq_invHidSet (Q : (recHwSpec X Z S M').Port → Prop) [DecidablePred Q]
    (Inv : HwReg X Z (Finset S × M') → Prop) (Hh : Set Z) (Hk Hk' : Set X)
    (i : (recHwSpec X Z S M').Port) (E : QReg)
    (σ : Matrix (((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M'))) × E)
      (((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M'))) × E) ℂ)
    (hσ : Q i → ∀ a, ¬Inv a.1.2 → σ a a = 0) :
    portMass Q Hh Hk Hk' i (MatrixMap.traceRight _ E σ) =
      diagMass (invHidSet Q Inv Hh Hk Hk' i) (MatrixMap.traceRight _ E σ) := by
  by_cases hQ : Q i
  · simp only [portMass, invHidSet, hQ, ↓reduceIte]
    rw [congrFun (congrFun (extWeight_hiddenMass_eq (t := recSpec S M') Hh Hk Hk') i) _]
    refine diagMass_eq_inter _ _ fun a ha ↦ traceRight_diag_eq_zero fun e ↦ ?_
    exact hσ hQ (a, e) ha
  · simp only [portMass, invHidSet, hQ, ↓reduceIte]
    exact (Finset.sum_eq_zero fun a _ ↦ Set.indicator_of_notMem (Set.notMem_empty a) _).symm

/-- **Disclose's per-call hidden-mass bound for `runtimeR` on an invariant**
(`sum_queryWeight_portMass_runtimeR_le` with the sources asked only on the states of `Inv v`,
which the inputs of the calls of the ports `Q` satisfy). -/
theorem sum_queryWeight_portMass_runtimeR_le_inv (Q : (recHwSpec X Z S M').Port → Prop)
    [DecidablePred Q] (m₀ : Finset S × M') (lab : HwReg X Z (Finset S × M') → Finset Sv)
    (x : ((s : Sv) → Dv s) → QuantumComp Λ (recHwSpec X Z S M') Xf A)
    (ρ : ((s : Sv) → Dv s) → Matrix (A × QReg.of (HwReg X Z (Finset S × M')))
      (A × QReg.of (HwReg X Z (Finset S × M'))) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (hview : ViewByOn (runtimeR m₀) I (fun i ↦ i.isLeft = true) lab x ρ j)
    (Inv : ((s : Sv) → Dv s) → HwReg X Z (Finset S × M') → Prop)
    (hinv : ∀ v, (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (Inv v)) (x v) (ρ v))
    (Hhv : ((s : Sv) → Dv s) → Set Z) (Hkv Hk'v : ((s : Sv) → Dv s) → Set X) (κ : ℝ≥0∞)
    (src : Sources X Z S M' Sv Dv lab Inv Hhv Hkv Hk'v κ) :
    ∑ v, (runtimeR m₀).queryWeight I (portMass Q (Hhv v) (Hkv v) (Hk'v v)) (x v) (ρ v) j ≤
      κ * ∑ v, (runtimeR m₀).queryWeight I
        (fun i σ ↦ if Q i then ENNReal.ofReal σ.trace.re else 0) (x v) (ρ v) j := by
  have hw : ∀ v, (runtimeR m₀).queryWeight I (portMass Q (Hhv v) (Hkv v) (Hk'v v)) (x v) (ρ v) j =
      (runtimeR m₀).queryWeight I
        (fun i ↦ diagMass (invHidSet Q (Inv v) (Hhv v) (Hkv v) (Hk'v v) i)) (x v) (ρ v) j :=
    fun v ↦ queryWeight_congr_of_forallQueries (runtimeR m₀) I
      (P := invSupp (runtimeR m₀) Q (Inv v))
      (w := portMass Q (Hhv v) (Hkv v) (Hk'v v))
      (w' := fun i ↦ diagMass (invHidSet Q (Inv v) (Hhv v) (Hkv v) (Hk'v v) i))
      (fun i E σ hσ ↦ portMass_eq_invHidSet Q (Inv v) _ _ _ i E σ hσ) (x v) (ρ v) (hinv v) j
  rw [Finset.sum_congr rfl fun v _ ↦ hw v]
  refine sum_queryWeight_view_le_on (runtimeR m₀) I lab x ρ hρ j _ hview Q
    (fun v i ↦ invHidSet Q (Inv v) (Hhv v) (Hkv v) (Hk'v v) i)
    (fun v i hi ↦ ?_) (fun v i hi ↦ by simp only [invHidSet, hi, ↓reduceIte]; rfl)
    (sumPort (liftCells src.sh src.sk src.sk' ∅) fun _ _ ↦ ∅)
    (sumPort (liftCells src.Fh src.Fk src.Fk' fun _ _ ↦ ∅) fun _ _ _ _ ↦ ∅) (fun i p s v d ↦ ?_)
    (fun v i p hp ↦ ?_) κ (fun i p v ↦ ?_)
  · rcases i with i | T
    · exact absurd rfl hi
    · by_cases hQi : Q (Sum.inr T)
      · simp only [invHidSet, hQi, ↓reduceIte]
        exact Set.empty_inter _
      · simp only [invHidSet, hQi, ↓reduceIte]
        rfl
  · rcases i with (((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c) | T
    · exact src.hFh _ _ s v d
    · exact src.hFk _ _ s v d
    · exact src.hFk' _ _ s v d
    · exact src.hFh _ _ s v d
    · exact src.hFk _ _ s v d
    · exact src.hFk' _ _ s v d
    · rfl
    · rfl
  · by_cases hQi : Q i
    · simp only [invHidSet, hQi, ↓reduceIte] at hp
      obtain ⟨hp, hI⟩ := hp
      rcases i with (((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c) | T
      · exact src.hh v _ _ hI hp.1 hp.2
      · exact src.hk v _ _ hI hp.1 hp.2
      · exact src.hk' v _ _ hI hp.1 hp.2
      · exact src.hh v _ _ hI hp.1 hp.2
      · exact src.hk v _ _ hI hp.1 hp.2
      · exact src.hk' v _ _ hI hp.1 hp.2
      · exact hp.elim
      · exact hp.elim
    · simp only [invHidSet, hQi, ↓reduceIte] at hp
      exact hp.elim
  · rcases i with (((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c) | T
    · exact src.hκh _ _ v
    · exact src.hκk _ _ v
    · exact src.hκk' _ _ v
    · exact src.hκh _ _ v
    · exact src.hκk _ _ v
    · exact src.hκk' _ _ v
    · simp [sumPort, liftCells]
    · simp [sumPort]

/-- **The total hidden mass at the ports `Q` for `runtimeR`, on an invariant**: with at most `q`
calls of the ports `Q` on every path, summed over all calls and the hidden values, at most `κ q`
times the traces. -/
theorem sum_totalWeight_portMass_runtimeR_le_inv (Q : (recHwSpec X Z S M').Port → Prop)
    [DecidablePred Q] (m₀ : Finset S × M') (lab : HwReg X Z (Finset S × M') → Finset Sv)
    (x : ((s : Sv) → Dv s) → QuantumComp Λ (recHwSpec X Z S M') Xf A)
    (ρ : ((s : Sv) → Dv s) → Matrix (A × QReg.of (HwReg X Z (Finset S × M')))
      (A × QReg.of (HwReg X Z (Finset S × M'))) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef)
    (hview : ∀ j, ViewByOn (runtimeR m₀) I (fun i ↦ i.isLeft = true) lab x ρ j)
    (Inv : ((s : Sv) → Dv s) → HwReg X Z (Finset S × M') → Prop)
    (hinv : ∀ v, (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (Inv v)) (x v) (ρ v))
    (Hhv : ((s : Sv) → Dv s) → Set Z) (Hkv Hk'v : ((s : Sv) → Dv s) → Set X) (κ : ℝ≥0∞)
    (src : Sources X Z S M' Sv Dv lab Inv Hhv Hkv Hk'v κ) {q : ℕ}
    (hq : ∀ v, IFreeM.IsChargeBound (x v) (portCharge fun i ↦ if Q i then 1 else 0) q) :
    ∑ v, (runtimeR m₀).totalWeight I (portMass Q (Hhv v) (Hkv v) (Hk'v v)) (x v) (ρ v) ≤
      κ * (q * ∑ v, ENNReal.ofReal (ρ v).trace.re) := by
  refine (sum_totalWeight_le_of_forall (runtimeR m₀) I _ _ x ρ κ fun j ↦
    sum_queryWeight_portMass_runtimeR_le_inv I Q m₀ lab x ρ hρ j (hview j) Inv hinv Hhv Hkv Hk'v
      κ src).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun v _ ↦
    totalWeight_trace_le_of_isChargeBound' (runtimeR m₀) I Q (x v) (hq v) (hρ v)

omit [Nonempty X] [Nonempty Z] [AddCommGroup X] [AddCommGroup Z] in
/-- The hidden mass at the ports `Q` is at most the trace there. -/
theorem portMass_le_trace (Q : (recHwSpec X Z S M').Port → Prop) [DecidablePred Q]
    (Hh : Set Z) (Hk Hk' : Set X) (i : (recHwSpec X Z S M').Port)
    {σ : Matrix ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M')))
      ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M'))) ℂ} (hσ : σ.PosSemidef) :
    portMass Q Hh Hk Hk' i σ ≤ if Q i then ENNReal.ofReal σ.trace.re else 0 := by
  by_cases hQ : Q i
  · simp only [portMass, hQ, ↓reduceIte]
    rw [congrFun (congrFun (extWeight_hiddenMass_eq (t := recSpec S M') Hh Hk Hk') i) σ]
    exact diagMass_le _ hσ
  · simp only [portMass, hQ, ↓reduceIte, le_refl]

/-- **Every call's hidden mass is at most its trace**: with at most `q` calls of the ports `Q`,
the total hidden mass at them is at most `q` times the trace. -/
theorem totalWeight_portMass_le (Q : (recHwSpec X Z S M').Port → Prop) [DecidablePred Q]
    (m₀ : Finset S × M') (Hh : Set Z) (Hk Hk' : Set X)
    (x : QuantumComp Λ (recHwSpec X Z S M') Xf A)
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M'))) (A × QReg.of (HwReg X Z (Finset S × M')))
      ℂ} (hρ : ρ.PosSemidef) {q : ℕ}
    (hq : IFreeM.IsChargeBound x (portCharge fun i ↦ if Q i then 1 else 0) q) :
    (runtimeR m₀).totalWeight I (portMass Q Hh Hk Hk') x ρ ≤ q * ENNReal.ofReal ρ.trace.re :=
  (ENNReal.tsum_le_tsum fun j ↦ (runtimeR m₀).queryWeight_mono I
    (fun i _ hσ ↦ portMass_le_trace Q Hh Hk Hk' i hσ) x hρ j).trans
    (totalWeight_trace_le_of_isChargeBound' (runtimeR m₀) I Q x hq hρ)

/-- The hidden mass is monotone in the hidden sets. -/
theorem totalWeight_portMass_mono (Q : (recHwSpec X Z S M').Port → Prop) [DecidablePred Q]
    (m₀ : Finset S × M') {Hh Hh₂ : Set Z} {Hk Hk₂ Hk' Hk'₂ : Set X} (hh : Hh ⊆ Hh₂)
    (hk : Hk ⊆ Hk₂) (hk' : Hk' ⊆ Hk'₂) (x : QuantumComp Λ (recHwSpec X Z S M') Xf A)
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M'))) (A × QReg.of (HwReg X Z (Finset S × M')))
      ℂ} (hρ : ρ.PosSemidef) :
    (runtimeR m₀).totalWeight I (portMass Q Hh Hk Hk') x ρ ≤
      (runtimeR m₀).totalWeight I (portMass Q Hh₂ Hk₂ Hk'₂) x ρ := by
  refine ENNReal.tsum_le_tsum fun j ↦ (runtimeR m₀).queryWeight_mono I (fun i σ _ ↦ ?_) x hρ j
  by_cases hQ : Q i
  · simp only [portMass, hQ, ↓reduceIte]
    rw [congrFun (congrFun (extWeight_hiddenMass_eq (t := recSpec S M') Hh Hk Hk') i) σ,
      congrFun (congrFun (extWeight_hiddenMass_eq (t := recSpec S M') Hh₂ Hk₂ Hk'₂) i) σ]
    refine diagMass_mono ?_ σ
    rcases i with (((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c) | T
    · exact fun p hp ↦ ⟨hh hp.1, hp.2⟩
    · exact fun p hp ↦ ⟨hk hp.1, hp.2⟩
    · exact fun p hp ↦ ⟨hk' hp.1, hp.2⟩
    · exact fun p hp ↦ ⟨hh hp.1, hp.2⟩
    · exact fun p hp ↦ ⟨hk hp.1, hp.2⟩
    · exact fun p hp ↦ ⟨hk' hp.1, hp.2⟩
    · exact fun p hp ↦ hp
    · exact fun p hp ↦ hp
  · simp only [portMass, hQ, ↓reduceIte, le_refl]

/-- **Hidden sets added by union**: the hidden mass of the union is at most the sum. -/
theorem totalWeight_portMass_union_le (Q : (recHwSpec X Z S M').Port → Prop) [DecidablePred Q]
    (m₀ : Finset S × M') (Hh Hh₂ : Set Z) (Hk Hk₂ Hk' Hk'₂ : Set X)
    (x : QuantumComp Λ (recHwSpec X Z S M') Xf A)
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M'))) (A × QReg.of (HwReg X Z (Finset S × M')))
      ℂ} (hρ : ρ.PosSemidef) :
    (runtimeR m₀).totalWeight I (portMass Q (Hh ∪ Hh₂) (Hk ∪ Hk₂) (Hk' ∪ Hk'₂)) x ρ ≤
      (runtimeR m₀).totalWeight I (portMass Q Hh Hk Hk') x ρ +
        (runtimeR m₀).totalWeight I (portMass Q Hh₂ Hk₂ Hk'₂) x ρ := by
  simp only [QuantumRuntime.totalWeight]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun j ↦ ((runtimeR m₀).queryWeight_mono I
    (w' := fun i σ ↦ portMass Q Hh Hk Hk' i σ + portMass Q Hh₂ Hk₂ Hk'₂ i σ)
    (fun i σ _ ↦ ?_) x hρ j).trans_eq (Hybrid.queryWeight_add (runtimeR m₀) I _ _ x ρ j)
  by_cases hQ : Q i
  · simp only [portMass, hQ, ↓reduceIte]
    rw [congrFun (congrFun (extWeight_hiddenMass_eq (t := recSpec S M') Hh Hk Hk') i) σ,
      congrFun (congrFun (extWeight_hiddenMass_eq (t := recSpec S M') Hh₂ Hk₂ Hk'₂) i) σ,
      congrFun (congrFun (extWeight_hiddenMass_eq (t := recSpec S M') (Hh ∪ Hh₂) (Hk ∪ Hk₂)
        (Hk' ∪ Hk'₂)) i) σ]
    refine (diagMass_mono ?_ σ).trans (diagMass_union_le _ _ σ)
    rcases i with (((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c) | T
    · exact fun p hp ↦ hp.1.elim (fun h ↦ Or.inl ⟨h, hp.2⟩) fun h ↦ Or.inr ⟨h, hp.2⟩
    · exact fun p hp ↦ hp.1.elim (fun h ↦ Or.inl ⟨h, hp.2⟩) fun h ↦ Or.inr ⟨h, hp.2⟩
    · exact fun p hp ↦ hp.1.elim (fun h ↦ Or.inl ⟨h, hp.2⟩) fun h ↦ Or.inr ⟨h, hp.2⟩
    · exact fun p hp ↦ hp.1.elim (fun h ↦ Or.inl ⟨h, hp.2⟩) fun h ↦ Or.inr ⟨h, hp.2⟩
    · exact fun p hp ↦ hp.1.elim (fun h ↦ Or.inl ⟨h, hp.2⟩) fun h ↦ Or.inr ⟨h, hp.2⟩
    · exact fun p hp ↦ hp.1.elim (fun h ↦ Or.inl ⟨h, hp.2⟩) fun h ↦ Or.inr ⟨h, hp.2⟩
    · exact fun p hp ↦ hp.elim
    · exact fun p hp ↦ hp.elim
  · simp only [portMass, hQ, ↓reduceIte, add_zero, le_refl]

end runtimeR

/-! ## Averages through a reparametrization on a good set -/

section avg

/-- **The table average through an injection on a good set.** The table `Θ`, padded by `E`, is
mapped by `e` into public data `P` and hidden values `V`, injectively on the good set `G`, with
`|P| |V| ≤ |Θ| |E|`. If `f ≤ g ∘ e` on `G`, `f ≤ c` off `G`, and for every public datum the hidden
values sum `g` to at most `κ |V|`, then the average of `f` is at most `κ` plus `c` times the bad
fraction. -/
theorem uavg_le_of_injOn {Θ E P V : Type*} [Fintype Θ] [Fintype E] [Nonempty E] [Fintype P]
    [Fintype V] (e : Θ × E → P × V) (G : Θ × E → Prop) [DecidablePred G]
    (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card V ≤ Fintype.card (Θ × E))
    (f : Θ → ℝ≥0∞) (g : P → V → ℝ≥0∞) (hfg : ∀ t, G t → f t.1 ≤ g (e t).1 (e t).2)
    (c : ℝ≥0∞) (hf : ∀ t, ¬G t → f t.1 ≤ c) (κ : ℝ≥0∞)
    (hg : ∀ p, ∑ v, g p v ≤ κ * Fintype.card V) :
    uavg f ≤ κ + c * ((Fintype.card (Θ × E) : ℝ≥0∞)⁻¹ *
      (Finset.univ.filter fun t ↦ ¬G t).card) := by
  classical
  set N : ℝ≥0∞ := (Fintype.card (Θ × E) : ℝ≥0∞)
  have hsplit : ∑ t : Θ × E, f t.1 ≤
      ∑ t ∈ Finset.univ.filter G, g (e t).1 (e t).2 +
        ∑ _t ∈ Finset.univ.filter fun t ↦ ¬G t, c := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ G]
    exact add_le_add (Finset.sum_le_sum fun t ht ↦ hfg t (Finset.mem_filter.mp ht).2)
      (Finset.sum_le_sum fun t ht ↦ hf t (Finset.mem_filter.mp ht).2)
  have hgood : ∑ t ∈ Finset.univ.filter G, g (e t).1 (e t).2 ≤ κ * N := by
    have himg : ∑ t ∈ Finset.univ.filter G, g (e t).1 (e t).2 =
        ∑ y ∈ (Finset.univ.filter G).image e, g y.1 y.2 := by
      refine (Finset.sum_image (f := fun y : P × V ↦ g y.1 y.2) ?_).symm
      intro a ha b hb h
      exact hinj (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2 h
    calc ∑ t ∈ Finset.univ.filter G, g (e t).1 (e t).2
        ≤ ∑ y : P × V, g y.1 y.2 := by
          rw [himg]
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = ∑ p, ∑ v, g p v := Fintype.sum_prod_type _
      _ ≤ ∑ _p : P, κ * Fintype.card V := Finset.sum_le_sum fun p _ ↦ hg p
      _ = κ * ((Fintype.card P : ℝ≥0∞) * Fintype.card V) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ κ * N := mul_le_mul_of_nonneg_left (by rw [← Nat.cast_mul]; exact Nat.cast_le.mpr hcard)
          zero_le
  rw [← uavg_pad (P := E) f]
  unfold uavg
  calc (N)⁻¹ * ∑ t : Θ × E, f t.1
      ≤ N⁻¹ * (κ * N + c * (Finset.univ.filter fun t ↦ ¬G t).card) := by
        gcongr
        refine hsplit.trans (add_le_add hgood (le_of_eq ?_))
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = κ * (N⁻¹ * N) + c * (N⁻¹ * (Finset.univ.filter fun t ↦ ¬G t).card) := by ring
    _ ≤ κ + c * (N⁻¹ * (Finset.univ.filter fun t ↦ ¬G t).card) := by
        have hN1 : N⁻¹ * N ≤ 1 := by
          by_cases h0 : N = 0
          · simp [h0]
          · rw [ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _)]
        exact add_le_add ((mul_le_mul_of_nonneg_left hN1 zero_le).trans_eq (mul_one κ)) le_rfl

end avg

/-! ## leanXMSS: the hidden sets and the averaged masses -/

section xmss

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- **The program ports of the honest paths** the template game calls at the table `L` (in-table
keys), realized (GameT's `progSet`, the same set). -/
def pathProgs (L : HonestTable) : Set (HwProg X Z) :=
  {c | ∃ (l : Layer) (e : KeyIndex) (w : Encoding) (s : Slot), e.val < keyCount l ∧
    s ∈ layerSlots l e w ∧ ∃ p ∈ slotPorts (pubOf L) s, p.realize (valueAt L) = c}

/-- The `h`-cells of the honest paths. -/
def pathH (L : HonestTable) : Set Z :=
  {z | ∃ a, HwProg.programH z a ∈ pathProgs L}

/-- The `k`-cells of the honest paths. -/
def pathK (L : HonestTable) : Set X :=
  {x | ∃ a, HwProg.programK x a ∈ pathProgs L}

/-- The `k'`-cells of the honest paths. -/
def pathK' (L : HonestTable) : Set X :=
  {x | ∃ a, HwProg.programK' x a ∈ pathProgs L}

/-- **`covers`**: a table whose cells are cells of the honest paths (GameT's `tableHw L`, whose
cells are exactly those programmed by `progSet L = pathProgs L`) is covered by the path cells,
with any further hidden sets added. -/
theorem covers_of_progs (W : Hw X Z) (L : HonestTable) (Eh : Set Z) (Ek Ek' : Set X)
    (hh : ∀ z, W.1 z ≠ none → ∃ a, HwProg.programH z a ∈ pathProgs L)
    (hk : ∀ x, W.2.1 x ≠ none → ∃ a, HwProg.programK x a ∈ pathProgs L)
    (hk' : ∀ x, W.2.2 x ≠ none → ∃ a, HwProg.programK' x a ∈ pathProgs L) :
    Covers W (pathH L ∪ Eh) (pathK L ∪ Ek) (pathK' L ∪ Ek') :=
  ⟨fun z hz ↦ Or.inl (hh z hz), fun x hx ↦ Or.inl (hk x hx), fun x hx ↦ Or.inl (hk' x hx)⟩

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **The averaged total hidden mass at the ports `Q` of the realized template game.**

The table, padded by `E`, is mapped by `e` into public data `P` and hidden values, injectively on
the good set `G` (the reparametrization: Reparam's `fwd` composed with SchemeSplit for the chain
starts). On `G` the game at the table is the template game at the public data `pubP` realized at
the hidden values (`hgame`, Reparam's `rounds_fwd`), and the hidden sets lie in sets `Hhv`, `Hkv`,
`Hk'v` of the public data and hidden values. The inputs of the calls of the ports `Q` lie in the
invariant `Inv`, on which the hidden cells have sources weighing at most `κ` (`Sources`, for every
public datum). With at most `N` calls of the ports `Q`, the averaged total hidden mass is at most
`N κ` plus `N` times the bad fraction. -/
theorem uavg_totalWeight_portMass_le (Q : (recHwSpec X Z ValPos M).Port → Prop) [DecidablePred Q]
    (A : Adversary (X × Z)) (m₀ : Finset ValPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset ValPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset ValPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (Hh : HonestTable → Set Z) (Hk Hk' : HonestTable → Set X)
    {E P : Type} [Fintype E] [Nonempty E] [Fintype P]
    (e : HonestTable × E → P × (ValPos → Digest)) (G : HonestTable × E → Prop) [DecidablePred G]
    (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card (ValPos → Digest) ≤ Fintype.card (HonestTable × E))
    (pubP : P → Pub)
    (hgame : ∀ t, G t → realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) =
      realizeT (e t).2 (gameT M upd (pubP (e t).1) A))
    (Hhv : P → (ValPos → Digest) → Set Z) (Hkv Hk'v : P → (ValPos → Digest) → Set X)
    (hsub : ∀ t, G t → Hh t.1 ⊆ Hhv (e t).1 (e t).2 ∧ Hk t.1 ⊆ Hkv (e t).1 (e t).2 ∧
      Hk' t.1 ⊆ Hk'v (e t).1 (e t).2)
    (Inv : P → (ValPos → Digest) → HwReg X Z (Finset ValPos × M) → Prop)
    (hinv : ∀ p v, (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q (Inv p v)) (realizeT v (gameT M upd (pubP p) A)) ρ)
    (κ : ℝ≥0∞)
    (src : ∀ p, Sources X Z ValPos M ValPos XD (fun r ↦ r.2.2.1) (Inv p) (Hhv p) (Hkv p)
      (Hk'v p) κ)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : ValPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
        (portCharge fun i ↦ if Q i then 1 else 0) N) :
    uavg (fun L : HonestTable ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass Q (Hh L) (Hk L) (Hk' L)) (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ) ≤
      N * κ + N * ((Fintype.card (HonestTable × E) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ ¬G t).card) := by
  have hbound : ∀ (pub : Pub) (v : ValPos → Digest) (Hh₀ : Set Z) (Hk₀ Hk'₀ : Set X),
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments (portMass Q Hh₀ Hk₀ Hk'₀)
        (realizeT v (gameT M upd pub A)) ρ ≤ N :=
    fun pub v Hh₀ Hk₀ Hk'₀ ↦ (totalWeight_portMass_le _ Q m₀ Hh₀ Hk₀ Hk'₀ _ hρ (hN pub v)).trans
      ((mul_le_mul_of_nonneg_left hρ1 zero_le).trans_eq (mul_one _))
  refine (uavg_le_of_injOn e G hinj hcard _
    (fun p v ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass Q (Hhv p v) (Hkv p v) (Hk'v p v)) (realizeT v (gameT M upd (pubP p) A)) ρ)
    (fun t ht ↦ ?_) N (fun t _ ↦ hbound _ _ _ _ _) (κ * N) fun p ↦ ?_).trans ?_
  · rw [hgame t ht]
    obtain ⟨h1, h2, h3⟩ := hsub t ht
    exact totalWeight_portMass_mono _ Q m₀ h1 h2 h3 _ hρ
  · refine (sum_totalWeight_portMass_runtimeR_le_inv LocalSig.Interp.instruments Q m₀
      (fun r ↦ r.2.2.1) (fun v ↦ realizeT v (gameT M upd (pubP p) A)) (fun _ ↦ ρ) (fun _ ↦ hρ)
      (fun j ↦ viewByOn_gameT M upd (pubP p) A m₀ ρ j) (Inv p) (hinv p) (Hhv p) (Hkv p)
      (Hk'v p) κ (src p) (fun v ↦ hN (pubP p) v)).trans ?_
    calc κ * (N * ∑ _v : ValPos → Digest, ENNReal.ofReal ρ.trace.re)
        ≤ κ * (N * ∑ _v : ValPos → Digest, (1 : ℝ≥0∞)) := by gcongr
      _ = κ * N * Fintype.card (ValPos → Digest) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_assoc]
  · rw [mul_comm κ]

/-- **`hybSponge`**: the averaged total hidden mass at the sponge ports (`spongeMass`) of the
realized template game with at most `N` sponge calls (`6 q` for `q` adversary calls) is at most
`N (κ + bad)`. -/
theorem uavg_spongeMass_le (A : Adversary (X × Z)) (m₀ : Finset ValPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset ValPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset ValPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (Hh : HonestTable → Set Z) (Hk Hk' : HonestTable → Set X)
    {E P : Type} [Fintype E] [Nonempty E] [Fintype P]
    (e : HonestTable × E → P × (ValPos → Digest)) (G : HonestTable × E → Prop) [DecidablePred G]
    (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card (ValPos → Digest) ≤ Fintype.card (HonestTable × E))
    (pubP : P → Pub)
    (hgame : ∀ t, G t → realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) =
      realizeT (e t).2 (gameT M upd (pubP (e t).1) A))
    (Hhv : P → (ValPos → Digest) → Set Z) (Hkv Hk'v : P → (ValPos → Digest) → Set X)
    (hsub : ∀ t, G t → Hh t.1 ⊆ Hhv (e t).1 (e t).2 ∧ Hk t.1 ⊆ Hkv (e t).1 (e t).2 ∧
      Hk' t.1 ⊆ Hk'v (e t).1 (e t).2)
    (Inv : P → (ValPos → Digest) → HwReg X Z (Finset ValPos × M) → Prop)
    (hinv : ∀ p v, (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) (fun i ↦ extCls X Z (Finset ValPos × M) (recSpec ValPos M) i = false)
        (Inv p v)) (realizeT v (gameT M upd (pubP p) A)) ρ)
    (κ : ℝ≥0∞)
    (src : ∀ p, Sources X Z ValPos M ValPos XD (fun r ↦ r.2.2.1) (Inv p) (Hhv p) (Hkv p)
      (Hk'v p) κ)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : ValPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
        (portCharge fun i ↦ if extCls X Z (Finset ValPos × M) (recSpec ValPos M) i then 0 else 1)
        N) :
    uavg (fun L : HonestTable ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (spongeMass (Hh L) (Hk L) (Hk' L)) (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ) ≤
      N * κ + N * ((Fintype.card (HonestTable × E) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ ¬G t).card) := by
  have hc : (fun i ↦ if extCls X Z (Finset ValPos × M) (recSpec ValPos M) i = false then 1 else 0) =
      fun i ↦ if extCls X Z (Finset ValPos × M) (recSpec ValPos M) i then 0 else 1 :=
    funext fun i ↦ by cases extCls X Z (Finset ValPos × M) (recSpec ValPos M) i <;> rfl
  exact uavg_totalWeight_portMass_le upd _ A m₀ ρ hρ hρ1 Hh Hk Hk' e G hinj hcard pubP hgame Hhv
    Hkv Hk'v hsub Inv hinv κ src fun pub v ↦ by rw [hc]; exact hN pub v

/-- **`hybRead`**: the averaged total hidden mass at the read ports (`readMass`) of the realized
template game with at most `N` classical calls (`clsCap`) is at most `N (κ + bad)`. -/
theorem uavg_readMass_le (A : Adversary (X × Z)) (m₀ : Finset ValPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset ValPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset ValPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (Hh : HonestTable → Set Z) (Hk Hk' : HonestTable → Set X)
    {E P : Type} [Fintype E] [Nonempty E] [Fintype P]
    (e : HonestTable × E → P × (ValPos → Digest)) (G : HonestTable × E → Prop) [DecidablePred G]
    (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card (ValPos → Digest) ≤ Fintype.card (HonestTable × E))
    (pubP : P → Pub)
    (hgame : ∀ t, G t → realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) =
      realizeT (e t).2 (gameT M upd (pubP (e t).1) A))
    (Hhv : P → (ValPos → Digest) → Set Z) (Hkv Hk'v : P → (ValPos → Digest) → Set X)
    (hsub : ∀ t, G t → Hh t.1 ⊆ Hhv (e t).1 (e t).2 ∧ Hk t.1 ⊆ Hkv (e t).1 (e t).2 ∧
      Hk' t.1 ⊆ Hk'v (e t).1 (e t).2)
    (Inv : P → (ValPos → Digest) → HwReg X Z (Finset ValPos × M) → Prop)
    (hinv : ∀ p v, (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) (fun i ↦ extCls X Z (Finset ValPos × M) (recSpec ValPos M) i = true)
        (Inv p v)) (realizeT v (gameT M upd (pubP p) A)) ρ)
    (κ : ℝ≥0∞)
    (src : ∀ p, Sources X Z ValPos M ValPos XD (fun r ↦ r.2.2.1) (Inv p) (Hhv p) (Hkv p)
      (Hk'v p) κ)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : ValPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
        (portCharge fun i ↦ if extCls X Z (Finset ValPos × M) (recSpec ValPos M) i then 1 else 0)
        N) :
    uavg (fun L : HonestTable ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (readMass (Hh L) (Hk L) (Hk' L)) (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ) ≤
      N * κ + N * ((Fintype.card (HonestTable × E) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ ¬G t).card) :=
  uavg_totalWeight_portMass_le upd _ A m₀ ρ hρ hρ1 Hh Hk Hk' e G hinj hcard pubP hgame Hhv Hkv
    Hk'v hsub Inv hinv κ src hN

end xmss

end Quantum.Xmss.Assembly

end
