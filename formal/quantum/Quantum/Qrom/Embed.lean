module

public import Quantum.Sponge.Oracle.Hardwired.Average

@[expose] public section

/-!
# A random oracle as port `h` of the sponge's three random functions

A random oracle `H : D → Y` (VCVio's `qromSpec D Y`) is port `h` of `spongeSpec Y D`: the sponge
framework with `X := Y` and `Z := D`, whose ports `k`, `k'` are never called. `liftH` relabels a
program's calls to port `h` (`hLens`); against the functions `(H, g, g')` it runs exactly as
against `H` (`run_spongeFnRuntime_liftH`), so its law in the QROM is its law in the sponge
experiment observed through `H` (`qromEvalDistMap_eq_spongeEvalDistMap_liftH`): the average over
the unused `g, g'` is trivial (`sum_inv_card_smul_fst`). Charges move along
(`isChargeBound_liftH_iff`, `isTotalQueryBound_liftH_iff`, `isChargeBound_liftOrdinary`), and the
hardwired runtime is run on the lifted program (`evalDistMap_hardwired_liftH`), with its register
and union view named at `(Y, D)` (`RomReg`, `hwCells`, `unionH`).
-/

open MeasureTheory IPFunctor
open scoped ENNReal

universe u v w

namespace Quantum.Qrom

open Quantum Quantum.Sponge

/-! ## Uniform averages over a product -/

/-- Averaging over a product a function of the first factor averages over the first factor. -/
theorem sum_inv_card_smul_fst {A B : Type*} [Fintype A] [Fintype B] [Nonempty B] {β : Type*}
    [AddCommMonoid β] [Module ℝ≥0∞ β] (G : A → β) :
    ∑ t : A × B, (Fintype.card (A × B) : ℝ≥0∞)⁻¹ • G t.1 =
      (Fintype.card A : ℝ≥0∞)⁻¹ • ∑ a, G a := by
  have hB : (Fintype.card B : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc : (Fintype.card B : ℝ≥0∞) * (Fintype.card (A × B) : ℝ≥0∞)⁻¹ =
      (Fintype.card A : ℝ≥0∞)⁻¹ := by
    rw [Fintype.card_prod, Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
      mul_left_comm, ENNReal.mul_inv_cancel hB (ENNReal.natCast_ne_top _), mul_one]
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  change ∑ _b : B, (Fintype.card (A × B) : ℝ≥0∞)⁻¹ • G a = _
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, hc]

variable {D Y : Type} [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y]

/-! ## Relabelling the oracle's port -/

variable (D Y) in
/-- The lens relabelling the only port of `qromSpec D Y` as port `h` of `spongeSpec Y D`. -/
def hLens {L : LocalSig.{u, v}} :
    Lens (QuantumComp.toIPFunctor L (qromSpec D Y)) (QuantumComp.toIPFunctor L (spongeSpec Y D))
    where
  toFunA _
    | .prim o => .prim o
    | .query _ E ℓ => .query .h E ℓ
  toFunB _ c := by cases c <;> exact id
  src_eq _ c _ := by cases c <;> rfl

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **A program over the random oracle as a program over port `h`.** -/
def liftH (x : QuantumComp L (qromSpec D Y) W A) : QuantumComp L (spongeSpec Y D) W A :=
  IFreeM.mapLens (hLens D Y) x

@[simp]
theorem liftH_pure (a : W A) :
    liftH (QuantumComp.pure a : QuantumComp L (qromSpec D Y) W A) = QuantumComp.pure a :=
  rfl

@[simp]
theorem liftH_primBind (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L (qromSpec D Y) W (L.next o b)) :
    liftH (QuantumComp.primBind o k) = QuantumComp.primBind o fun b ↦ liftH (k b) :=
  rfl

@[simp]
theorem liftH_queryBind (i : Unit) (E : QReg) (ℓ : A ≃ (qromSpec D Y).In i × E)
    (k : (qromSpec D Y).Result i →
      QuantumComp L (qromSpec D Y) W (QReg.of ((qromSpec D Y).Out i × E))) :
    liftH (QuantumComp.queryBind i E ℓ k) =
      QuantumComp.queryBind (spec := spongeSpec Y D) .h E ℓ fun r ↦ liftH (k r) :=
  rfl

/-! ## Charges -/

/-- **Charge transfer.** A charge `κ` of the sponge ports bounds the lifted program as the charge
`κ .h` of every call bounds the program. -/
theorem isChargeBound_liftH_iff (κ : SpongePort → ℕ) (x : QuantumComp L (qromSpec D Y) W A)
    (n : ℕ) :
    IFreeM.IsChargeBound (liftH x) (portCharge κ) n ↔
      IFreeM.IsChargeBound x (portCharge fun _ ↦ κ .h) n := by
  unfold IFreeM.IsChargeBound liftH IFreeM.mapLens
  refine (IFreeM.isRollBound_reindex_iff (hLens D Y).toReindexing (fun _ value ↦ value)
    (fun _ c ↦ by cases c <;> exact fun answer ↦ ⟨answer, rfl⟩) x n).trans ?_
  exact IFreeM.isRollBound_congr (fun _ c _ ↦ by cases c <;> rfl)
    (fun _ c _ ↦ by cases c <;> rfl)

/-- The lifted program makes as many calls as the program. -/
theorem isTotalQueryBound_liftH_iff (x : QuantumComp L (qromSpec D Y) W A) (n : ℕ) :
    (liftH x).IsTotalQueryBound n ↔ x.IsTotalQueryBound n := by
  unfold QuantumComp.IsTotalQueryBound IFreeM.IsChargeBound liftH IFreeM.mapLens
  refine (IFreeM.isRollBound_reindex_iff (hLens D Y).toReindexing (fun _ value ↦ value)
    (fun _ c ↦ by cases c <;> exact fun answer ↦ ⟨answer, rfl⟩) x n).trans ?_
  exact IFreeM.isRollBound_congr (fun _ c _ ↦ by cases c <;> rfl)
    (fun _ c _ ↦ by cases c <;> rfl)

omit [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y] in
/-- A charge of the left ports of a sum signature bounds the left-injected program. -/
theorem isChargeBound_liftOrdinary {s : QuantumOracleSpec.{0, 0}} {t : QuantumOracleSpec.{0, 0}}
    (κ : (s.sum t).Port → ℕ) {y : QuantumComp L s W A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge fun i ↦ κ (.inl i)) n) :
    IFreeM.IsChargeBound (y.liftOrdinary (t := t)) (portCharge κ) n := by
  refine IFreeM.IsChargeBound.mapLens QuantumComp.ordinaryLens ?_
  have he : (fun s' cmd ↦ portCharge (L := L) κ s' (QuantumComp.ordinaryLens.toFunA s' cmd)) =
      portCharge fun i ↦ κ (.inl i) := by
    funext s' cmd
    rcases cmd with o | ⟨i, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

/-! ## Runs and laws -/

variable [AddCommGroup D] [AddCommGroup Y]

/-- **Against `(H, g, g')`, the lifted program runs as the program against `H`.** -/
theorem run_spongeFnRuntime_liftH (H : D → Y) (g g' : Y → D) (I : L.Interp)
    (x : QuantumComp L (qromSpec D Y) W A) :
    (spongeFnRuntime H g g').run I (liftH x) = (additiveOracleRuntime H).run I x := by
  induction x using QuantumComp.inductionOn with
  | pure _ a =>
    rw [liftH_pure, QuantumRuntime.run_pure, QuantumRuntime.run_pure]
    rfl
  | primBind _ o k ih =>
    rw [liftH_primBind, QuantumRuntime.run_primBind, QuantumRuntime.run_primBind]
    exact congrArg _ (funext ih)
  | queryBind _ i E ℓ k ih =>
    rw [liftH_queryBind, QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind]
    exact congrArg (DSubInstrument.bind ((additiveOracleRuntime H).queryStep i E ℓ)) (funext ih)

/-- The lifted program has, against `(H, g, g')`, the observed law of the program against `H`. -/
theorem evalDistMap_spongeFnRuntime_liftH {γ : Type*} [MeasurableSpace γ] (H : D → Y)
    (g g' : Y → D) (I : L.Interp) (x : QuantumComp L (qromSpec D Y) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (spongeFnRuntime H g g').evalDistMap I (liftH x) ρ f =
      (additiveOracleRuntime H).evalDistMap I x ρ f := by
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.matrix_jointPost,
    run_spongeFnRuntime_liftH]
  rfl

/-- **The QROM is the sponge experiment on port `h`.** The law of a program against a uniform
random oracle `H : D → Y`, observed through `f H`, is the law of the lifted program against uniform
`(H, g, g')`, observed through `f H`. -/
theorem qromEvalDistMap_eq_spongeEvalDistMap_liftH {β : Type*} [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp L (qromSpec D Y) W A) (ρ : SubState A) (f : (D → Y) → (Σ u, W u) → β) :
    qromEvalDistMap I x ρ f = spongeEvalDistMap I (liftH x) ρ fun t ↦ f t.1 := by
  rw [qromEvalDistMap, sampledEvalDistMap_eq_sum, spongeEvalDistMap_eq_sum]
  simp only [evalDistMap_spongeFnRuntime_liftH]
  rw [← sum_inv_card_smul_fst (B := (Y → D) × (Y → D))
    fun H ↦ (additiveOracleRuntime H).evalDistMap I x ρ (f H), Finset.smul_sum]

/-! ## The hardwired register at `(Y, D)` -/

variable (D Y) in
/-- The register of the hardwired runtime for the random oracle: databases, hardwired cells and
memory, with the `k`, `k'` parts never used. -/
abbrev RomReg (M : Type) := HwReg Y D M

/-- Hardwired cells of `H` only. -/
def hwCells (w : Database D Y) : Hw Y D :=
  (w, Database.empty, Database.empty)

/-- The union view of the random oracle in a state of the hardwired register: the hardwired
value of a cell, else its database content. -/
def unionH {M : Type} (s : RomReg D Y M) (x : D) : Option Y :=
  (s.2.1.1 x).or (s.1.1 x)

omit [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y] [AddCommGroup D] [AddCommGroup Y] in
@[simp]
theorem unionH_apply {M : Type} (s : RomReg D Y M) (x : D) :
    unionH s x = (s.2.1.1 x).or (s.1.1 x) :=
  rfl

/-- **The lifted program against the hardwired runtime.** Runtime 1 started at `(∅, W₀, m₀)`
runs the lifted program as the experiment with the functions `overwrite W₀ (H, g, g')`. -/
theorem evalDistMap_hardwired_liftH {M : Type} [Fintype M] [DecidableEq M] {γ : Type*}
    [MeasurableSpace γ] (W₀ : Hw Y D) (m₀ : M) (I : L.Interp)
    (x : QuantumComp L (qromSpec D Y) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (spongeHardwiredReadRuntime Y D W₀ m₀).evalDistMap I (liftH x).liftOrdinary ρ f =
      (Fintype.card (D → Y) : ℝ≥0∞)⁻¹ • ∑ H : D → Y,
        (additiveOracleRuntime fun z ↦ (W₀.1 z).getD (H z)).evalDistMap I x ρ f := by
  rw [evalDistMap_hardwired_eq_avg]
  simp only [overwrite, evalDistMap_spongeFnRuntime_liftH]
  exact sum_inv_card_smul_fst (B := (Y → D) × (Y → D))
    fun H : D → Y ↦ (additiveOracleRuntime fun z ↦ (W₀.1 z).getD (H z)).evalDistMap I x ρ f

end Quantum.Qrom

end
