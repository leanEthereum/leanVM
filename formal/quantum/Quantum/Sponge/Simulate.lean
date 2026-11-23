module

public import Quantum.Decomposition
public import Quantum.Sponge.Spec
public import VCVio.Quantum.Comp.TotalQueryBound

@[expose] public section

/-!
# Simulating the permutation oracle by the three random functions

Lemma 6.2 of Alagic, Carolan, Majenz and Tokat, *The Sponge is Quantum Indifferentiable*
(ePrint 2025/731), for the oracle part: given `π`, a program in the quantum random-permutation
model on `S = X × Z` becomes a program against the oracles of `h`, `k`, `k'` that runs exactly as
the original against `φ = spongePerm (h, k, k') π = ω_h ∘ σ_k' ∘ π ∘ σ_k`.

* In place on a state register, `φ` is three calls and a local gate (`evalPerm`): `σ_k` is one
  call of port `k`, `π` a basis permutation, `σ_k'` one call of port `k'`, and `ω_h` one call of
  port `h` through the swap `X × Z ≃ Z × X`. Its inverse (`evalPermInv`) runs the inverse rounds
  in reverse order; each inverse round is the call conjugated by the local negation of its
  response (`|x, z⟩ ↦ |x, -z⟩ ↦ |x, -z + k x⟩ ↦ |x, z - k x⟩`).
* A call `|s, y⟩ ↦ |s, y + φ s⟩` of the forward port (`simCall`) copies `s` into a fresh state
  register `a`, evaluates `φ` in place on `a`, adds `a` into `y`, evaluates `φ⁻¹` in place on `a`,
  which returns it to `s`, and removes `a` by the adjoint of the copying isometry. The inverse port
  swaps `φ` and `φ⁻¹`. Each call costs six calls, two of each port.
* `simulate I π x` substitutes `simCall` for every call of `x` (PolyFun's
  `IPFunctor.IFreeM.substitute`, as VCVio's `Quantum.QuantumComp.embedCalls`) and turns the local
  operations of `x` into the instruments that `I` gives them, so `x` may be written over any
  primitive signature.

## Main statements

* `isQueryBound_simulate`: if every path of `x` makes at most `q` calls, every path of
  `simulate I π x` calls each of `h`, `k`, `k'` at most `2 * q` times.
* `run_simulate`: against the oracles of `(h, k, k')`, `simulate I π x` runs to the same dependent
  subinstrument as `x` against `spongePerm (h, k, k') π`; `evalDistMap_simulate` for observations.
* `qrpmEvalDistMap_eq_simulate`: the quantum random-permutation model is the average over `π` of
  the uniform-function experiment of `simulate I π x`, with observations that may read `φ`.

The removal of the copy of `s` is a contraction, not a channel, so `simulate I π x` is not
syntactically lossless, as for `embedCalls`; it runs losslessly whenever `x` does
(`lossless_run_simulate`).
-/

open MeasureTheory IPFunctor
open scoped ENNReal Kronecker Matrix

universe u v w u₁ v₁

namespace Quantum.Sponge

open Quantum

/-! ## Programs that run as basis maps -/

section runsAs

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {A B C : QReg}

/-- A program over instruments, ending on `B` with the unit value, runs against `R` as the basis
map `f` of the joint register: its run is conjugation by the basis matrix of `f`. -/
def RunsAs (x : QuantumComp₂ LocalSig.instruments.{v} spec A B Unit)
    (f : A × R.D → B × R.D) : Prop :=
  (R.run₂ .instruments x).branch () = MatrixMap.conj (basisMatrix f)

variable {R}

theorem RunsAs.congr {x : QuantumComp₂ LocalSig.instruments.{v} spec A B Unit}
    {f g : A × R.D → B × R.D} (hx : RunsAs R x f) (h : ∀ q, f q = g q) : RunsAs R x g := by
  rwa [← funext h]

/-- Sequencing runs the composite basis map. -/
theorem RunsAs.bind {x : QuantumComp₂ LocalSig.instruments.{v} spec A B Unit}
    {y : Unit → QuantumComp₂ LocalSig.instruments.{v} spec B C Unit} {f : A × R.D → B × R.D}
    {g : B × R.D → C × R.D} (hx : RunsAs R x f) (hy : RunsAs R (y ()) g) :
    RunsAs R (x.bind y) (g ∘ f) := by
  rw [RunsAs, QuantumRuntime.run₂_bind, SubInstrument.bind, DSubInstrument.branch_bind_unit, hx,
    hy, ← MatrixMap.conj_mul, ← basisMatrix_comp]

/-- The local gate of a basis injection `f`: the isometry `|a⟩ ↦ |f a⟩`. It is
`SubInstrument.ofIsometry` of the basis matrix of `f`, with its one outcome in the universe of the
instruments. -/
noncomputable def isoGate (f : A → B) (hf : Function.Injective f) :
    QuantumComp₂ LocalSig.instruments.{v} spec A B Unit :=
  QuantumComp₂.primBind (L := LocalSig.instruments.{v})
    ⟨PUnit, fun _ ↦ B, SubInstrument.ofMap (MatrixMap.conj (basisMatrix f))
      (MatrixMap.isCP_conj _) (MatrixMap.isTP_conj (conjTranspose_basisMatrix_mul_self hf)).isTNI⟩
    fun _ ↦ QuantumComp₂.pure ()

/-- The local contraction `⟨f b| ↦ ⟨b|` that reads the image of a basis injection `f` back: the
adjoint of `isoGate f`. -/
noncomputable def coGate (f : B → A) (hf : Function.Injective f) :
    QuantumComp₂ LocalSig.instruments.{v} spec A B Unit :=
  QuantumComp₂.primBind (L := LocalSig.instruments.{v})
    ⟨PUnit, fun _ ↦ B, SubInstrument.ofMap (MatrixMap.conj (basisMatrix f)ᴴ)
      (MatrixMap.isCP_conj _) (MatrixMap.isTNI_conj (posSemidef_one_sub_conjTranspose_mul_self (by
        rw [Matrix.conjTranspose_conjTranspose, conjTranspose_basisMatrix_mul_self hf])))⟩
    fun _ ↦ QuantumComp₂.pure ()

/-- A local operation with one outcome followed by `pure ()` runs as its branch, framed. -/
theorem branch_run₂_primBind_pure (p : SubInstrument A B PUnit.{v + 1}) :
    (R.run₂ .instruments (QuantumComp₂.primBind (L := LocalSig.instruments.{v})
      (spec := spec) ⟨PUnit, fun _ ↦ B, p⟩ fun _ ↦ QuantumComp₂.pure ())).branch () =
      (p.branch PUnit.unit).amplify R.D := by
  rw [QuantumRuntime.run₂_primBind, DSubInstrument.branch_bind_apply_univ, Fintype.sum_unique]
  simp only [QuantumRuntime.run₂_pure, SubInstrument.branch_pure_self, LinearMap.id_comp,
    DSubInstrument.branch_frame_apply, LocalSig.Interp.instruments_apply]

theorem runsAs_isoGate (f : A → B) (hf : Function.Injective f) :
    RunsAs R (isoGate.{v} (spec := spec) f hf) (Prod.map f id) := by
  rw [RunsAs, isoGate, branch_run₂_primBind_pure, SubInstrument.branch_ofMap,
    MatrixMap.amplify_conj, basisMatrix_kronecker_one]

/-- A program that runs as `Prod.map g id ∘ G`, followed by the contraction of `g`, runs as
`G`. -/
theorem RunsAs.bind_coGate {x : QuantumComp₂ LocalSig.instruments.{v} spec A C Unit}
    {F : A × R.D → C × R.D} (hx : RunsAs R x F) (g : B → C) (hg : Function.Injective g)
    (G : A × R.D → B × R.D) (hG : ∀ q, F q = Prod.map g id (G q)) :
    RunsAs R (x.bind fun _ ↦ coGate g hg) G := by
  rw [RunsAs, QuantumRuntime.run₂_bind, SubInstrument.bind, DSubInstrument.branch_bind_unit, hx,
    coGate, branch_run₂_primBind_pure, SubInstrument.branch_ofMap, MatrixMap.amplify_conj,
    ← MatrixMap.conj_mul, ← Matrix.conjTranspose_one, ← Matrix.conjTranspose_kronecker,
    basisMatrix_kronecker_one, show F = Prod.map g id ∘ G from funext hG,
    basisMatrix_comp, ← Matrix.mul_assoc,
    conjTranspose_basisMatrix_mul_self (hg.prodMap Function.injective_id), Matrix.one_mul]

end runsAs

/-! ## Calls of fixed oracles as basis maps -/

/-- The framed query of `H` is conjugation by the basis permutation of `H` beside the frame. -/
theorem branch_frame_oracleQuery {X' Y : Type*} [Fintype X'] [DecidableEq X'] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] (H : X' → Y) (F : Type*) [Fintype F] [DecidableEq F] :
    ((oracleQuery H).frame F).branch () =
      MatrixMap.conj (basisMatrix (Prod.map (oracleEquiv H) (id : F → F))) := by
  rw [DSubInstrument.branch_frame_apply, branch_oracleQuery_apply, MatrixMap.amplify_conj,
    oracleUnitary, basisMatrix_kronecker_one]

/-- A call against a step that is a basis map is the regrouped basis map. -/
theorem branch_queryStep_of_basis {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)
    {i : spec.Port} {r : spec.Result i} (g : spec.In i × R.D → spec.Out i × R.D)
    (hg : (R.step i).branch r = MatrixMap.conj (basisMatrix g)) (E : QReg) {A : QReg}
    (ℓ : A ≃ spec.In i × E) :
    (R.queryStep i E ℓ).branch r =
      MatrixMap.conj (basisMatrix (QuantumRuntime.queryEquivOut (spec.Out i) R.D E ∘
        Prod.map g id ∘ QuantumRuntime.queryEquivIn ℓ R.D)) := by
  rw [QuantumRuntime.queryStep_branch_eq_conj R hg, basisMatrix_kronecker_one,
    ← basisMatrix_comp, ← basisMatrix_comp]
  rfl

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X]
  [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

omit [AddCommGroup X] [AddCommGroup Z] in
/-- A call of a sponge port runs as its regrouped basis map, when the port's step is one. -/
theorem runsAs_query (R : QuantumRuntime (spongeSpec X Z)) (j : SpongePort)
    (g : spongeIn X Z j × R.D → spongeIn X Z j × R.D)
    (hg : (R.step j).branch () = MatrixMap.conj (basisMatrix g)) (E : QReg) {A : QReg}
    (ℓ : A ≃ spongeIn X Z j × E) :
    RunsAs R (QuantumComp₂.query (L := LocalSig.instruments.{v}) (spec := spongeSpec X Z) j E ℓ)
      (QuantumRuntime.queryEquivOut (spongeIn X Z j) R.D E ∘ Prod.map g id ∘
        QuantumRuntime.queryEquivIn ℓ R.D) := by
  rw [RunsAs, QuantumRuntime.run₂_query, SubInstrument.bind, DSubInstrument.branch_bind_unit,
    SubInstrument.branch_pure_self, LinearMap.id_comp]
  exact branch_queryStep_of_basis R g hg E ℓ

/-! ## `φ` and `φ⁻¹` in place -/

/-- The register of an in-place evaluation: the state `X × Z`, beside a remainder `F`. -/
abbrev stateReg (X Z : Type) [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (F : QReg) : QReg :=
  QReg.of ((X × Z) × F)

/-- The basis map that applies the permutation `e` to the state and leaves the rest. -/
def onState {F D : Type*} (e : Equiv.Perm (X × Z)) : ((X × Z) × F) × D → ((X × Z) × F) × D :=
  fun q ↦ ((e q.1.1, q.1.2), q.2)

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] in
theorem capacityRound_inv_apply (k : X → Z) (s : X × Z) :
    (capacityRound k)⁻¹ s = (s.1, s.2 - k s.1) := by
  rw [Equiv.Perm.inv_eq_iff_eq, capacityRound_apply, sub_add_cancel]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
theorem rateRound_inv_apply (h : Z → X) (s : X × Z) :
    (rateRound h)⁻¹ s = (s.1 - h s.2, s.2) := by
  rw [Equiv.Perm.inv_eq_iff_eq, rateRound_apply, sub_add_cancel]

/-- The negation `(x, z) ↦ (-x, z)` of the rate. -/
def negRate (X Z : Type) [AddCommGroup X] : Equiv.Perm (X × Z) :=
  (Equiv.neg X).prodCongr (Equiv.refl Z)

/-- The negation `(x, z) ↦ (x, -z)` of the capacity. -/
def negCap (X Z : Type) [AddCommGroup Z] : Equiv.Perm (X × Z) :=
  (Equiv.refl X).prodCongr (Equiv.neg Z)

variable (F : QReg)

/-- The local gate of a permutation of the state. -/
noncomputable def stateGate (e : Equiv.Perm (X × Z)) :
    QuantumComp₂ LocalSig.instruments.{v} (spongeSpec X Z) (stateReg X Z F) (stateReg X Z F)
      Unit :=
  isoGate (Prod.map e (id : F → F)) (e.injective.prodMap Function.injective_id)

/-- `σ_k`: one call of port `k` on the state. -/
noncomputable def sigmaK :
    QuantumComp₂ LocalSig.instruments.{v} (spongeSpec X Z) (stateReg X Z F) (stateReg X Z F)
      Unit :=
  QuantumComp₂.query (L := LocalSig.instruments.{v}) (spec := spongeSpec X Z) .k F (Equiv.refl _)

/-- `σ_k'`: one call of port `k'` on the state. -/
noncomputable def sigmaK' :
    QuantumComp₂ LocalSig.instruments.{v} (spongeSpec X Z) (stateReg X Z F) (stateReg X Z F)
      Unit :=
  QuantumComp₂.query (L := LocalSig.instruments.{v}) (spec := spongeSpec X Z) .k' F
    (Equiv.refl _)

/-- `ω_h`: one call of port `h` on the state, read as `Z × X` through the swap. -/
noncomputable def omegaH :
    QuantumComp₂ LocalSig.instruments.{v} (spongeSpec X Z) (stateReg X Z F) (stateReg X Z F)
      Unit :=
  (QuantumComp₂.query (L := LocalSig.instruments.{v}) (spec := spongeSpec X Z) .h F
    ((Equiv.prodComm X Z).prodCongr (Equiv.refl F))).bind fun _ ↦
      isoGate (A := QReg.of ((spongeSpec X Z).Out .h × F)) (B := stateReg X Z F)
        (Prod.map Prod.swap (id : F → F))
        (Prod.swap_injective.prodMap Function.injective_id)

/-- `σ_k⁻¹`: the call of `k` conjugated by the negation of the capacity. -/
noncomputable def sigmaKInv :
    QuantumComp₂ LocalSig.instruments.{v} (spongeSpec X Z) (stateReg X Z F) (stateReg X Z F)
      Unit :=
  (stateGate F (negCap X Z)).bind fun _ ↦ (sigmaK F).bind fun _ ↦ stateGate F (negCap X Z)

/-- `σ_k'⁻¹`: the call of `k'` conjugated by the negation of the capacity. -/
noncomputable def sigmaK'Inv :
    QuantumComp₂ LocalSig.instruments.{v} (spongeSpec X Z) (stateReg X Z F) (stateReg X Z F)
      Unit :=
  (stateGate F (negCap X Z)).bind fun _ ↦ (sigmaK' F).bind fun _ ↦ stateGate F (negCap X Z)

/-- `ω_h⁻¹`: the call of `h` conjugated by the negation of the rate. -/
noncomputable def omegaHInv :
    QuantumComp₂ LocalSig.instruments.{v} (spongeSpec X Z) (stateReg X Z F) (stateReg X Z F)
      Unit :=
  (stateGate F (negRate X Z)).bind fun _ ↦ (omegaH F).bind fun _ ↦ stateGate F (negRate X Z)

/-- **`φ` in place**: `σ_k`, the gate of `π`, `σ_k'`, `ω_h`; one call of each port. -/
noncomputable def evalPerm (π : Equiv.Perm (X × Z)) :
    QuantumComp₂ LocalSig.instruments.{v} (spongeSpec X Z) (stateReg X Z F) (stateReg X Z F)
      Unit :=
  (sigmaK F).bind fun _ ↦ (stateGate F π).bind fun _ ↦ (sigmaK' F).bind fun _ ↦ omegaH F

/-- **`φ⁻¹` in place**: `ω_h⁻¹`, `σ_k'⁻¹`, the gate of `π⁻¹`, `σ_k⁻¹`; one call of each port. -/
noncomputable def evalPermInv (π : Equiv.Perm (X × Z)) :
    QuantumComp₂ LocalSig.instruments.{v} (spongeSpec X Z) (stateReg X Z F) (stateReg X Z F)
      Unit :=
  (omegaHInv F).bind fun _ ↦ (sigmaK'Inv F).bind fun _ ↦ (stateGate F π⁻¹).bind fun _ ↦
    sigmaKInv F

/-- The in-place evaluation of the permutation behind a port of the permutation oracle: `φ` for
the forward port, `φ⁻¹` for the inverse port. -/
noncomputable def evalPort (π : Equiv.Perm (X × Z)) :
    PermutationPort →
      QuantumComp₂ LocalSig.instruments.{v} (spongeSpec X Z) (stateReg X Z F) (stateReg X Z F)
        Unit
  | .forward => evalPerm F π
  | .inverse => evalPermInv F π

section semantics

variable (h : Z → X) (k k' : X → Z)

theorem runsAs_stateGate (e : Equiv.Perm (X × Z)) :
    RunsAs (spongeFnRuntime h k k') (stateGate.{v} F e) (onState e) :=
  (runsAs_isoGate _ _).congr fun _ ↦ rfl

theorem runsAs_sigmaK :
    RunsAs (spongeFnRuntime h k k') (sigmaK.{v} F) (onState (capacityRound k)) := by
  unfold sigmaK
  exact (runsAs_query (spongeFnRuntime h k k') .k _ (branch_frame_oracleQuery k Unit) F
    _).congr fun _ ↦ rfl

theorem runsAs_sigmaK' :
    RunsAs (spongeFnRuntime h k k') (sigmaK'.{v} F) (onState (capacityRound k')) := by
  unfold sigmaK'
  exact (runsAs_query (spongeFnRuntime h k k') .k' _ (branch_frame_oracleQuery k' Unit) F
    _).congr fun _ ↦ rfl

theorem runsAs_omegaH :
    RunsAs (spongeFnRuntime h k k') (omegaH.{v} F) (onState (rateRound h)) := by
  unfold omegaH
  exact ((runsAs_query (spongeFnRuntime h k k') .h _ (branch_frame_oracleQuery h Unit) F
    _).bind (runsAs_isoGate _ _)).congr fun _ ↦ rfl

theorem runsAs_sigmaKInv :
    RunsAs (spongeFnRuntime h k k') (sigmaKInv.{v} F) (onState (capacityRound k)⁻¹) := by
  unfold sigmaKInv
  exact ((runsAs_stateGate F h k k' _).bind ((runsAs_sigmaK F h k k').bind
    (runsAs_stateGate F h k k' _))).congr fun q ↦ by
      simp [onState, negCap, capacityRound_inv_apply, sub_eq_add_neg, add_comm]

theorem runsAs_sigmaK'Inv :
    RunsAs (spongeFnRuntime h k k') (sigmaK'Inv.{v} F) (onState (capacityRound k')⁻¹) := by
  unfold sigmaK'Inv
  exact ((runsAs_stateGate F h k k' _).bind ((runsAs_sigmaK' F h k k').bind
    (runsAs_stateGate F h k k' _))).congr fun q ↦ by
      simp [onState, negCap, capacityRound_inv_apply, sub_eq_add_neg, add_comm]

theorem runsAs_omegaHInv :
    RunsAs (spongeFnRuntime h k k') (omegaHInv.{v} F) (onState (rateRound h)⁻¹) := by
  unfold omegaHInv
  exact ((runsAs_stateGate F h k k' _).bind ((runsAs_omegaH F h k k').bind
    (runsAs_stateGate F h k k' _))).congr fun q ↦ by
      simp [onState, negRate, rateRound_inv_apply, sub_eq_add_neg, add_comm]

theorem runsAs_evalPerm (π : Equiv.Perm (X × Z)) :
    RunsAs (spongeFnRuntime h k k') (evalPerm.{v} F π)
      (onState (spongePerm (h, k, k') π)) := by
  unfold evalPerm
  exact ((runsAs_sigmaK F h k k').bind ((runsAs_stateGate F h k k' π).bind
    ((runsAs_sigmaK' F h k k').bind (runsAs_omegaH F h k k')))).congr fun _ ↦ rfl

theorem runsAs_evalPermInv (π : Equiv.Perm (X × Z)) :
    RunsAs (spongeFnRuntime h k k') (evalPermInv.{v} F π)
      (onState (spongePerm (h, k, k') π)⁻¹) := by
  have hinv : (spongePerm (h, k, k') π)⁻¹ =
      (capacityRound k)⁻¹ * π⁻¹ * (capacityRound k')⁻¹ * (rateRound h)⁻¹ := by
    simp only [spongePerm, mul_inv_rev, mul_assoc]
  unfold evalPermInv
  rw [hinv]
  exact ((runsAs_omegaHInv F h k k').bind ((runsAs_sigmaK'Inv F h k k').bind
    ((runsAs_stateGate F h k k' π⁻¹).bind (runsAs_sigmaKInv F h k k')))).congr fun _ ↦ rfl

end semantics

/-! ## One call of the permutation oracle -/

/-- The permutation behind a port: `φ` for the forward port, `φ⁻¹` for the inverse port. -/
def portPerm (φ : Equiv.Perm (X × Z)) : PermutationPort → Equiv.Perm (X × Z)
  | .forward => φ
  | .inverse => φ⁻¹

/-- The other port. -/
def flipPort : PermutationPort → PermutationPort
  | .forward => .inverse
  | .inverse => .forward

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] in
theorem portPerm_flipPort_apply (φ : Equiv.Perm (X × Z)) (p : PermutationPort) (s : X × Z) :
    portPerm φ (flipPort p) (portPerm φ p s) = s := by
  cases p <;> simp [portPerm, flipPort]

variable {E : QReg}

/-- The register of the response of a call of the permutation oracle beside its remainder. -/
abbrev callReg (X Z : Type) [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (p : PermutationPort) (E : QReg) : QReg :=
  QReg.of ((qrpmSpec (X × Z)).Out p × E)

/-- Copy the query input `s` of a call into a fresh state register: `|s, y, e⟩ ↦ |s⟩|s, y, e⟩`. -/
def copyIn {p : PermutationPort} {A : QReg} (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) :
    A → stateReg X Z (callReg X Z p E) :=
  fun a ↦ (((ℓ a).1 : (X × Z) × (X × Z)).1, ℓ a)

omit [AddCommGroup X] [AddCommGroup Z] in
theorem copyIn_injective {p : PermutationPort} {A : QReg}
    (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) : Function.Injective (copyIn ℓ) :=
  fun _ _ hab ↦ ℓ.injective (congrArg Prod.snd hab)

/-- The basis map `|a⟩|s, y, e⟩ ↦ |a⟩|s, y + a, e⟩` that adds the state register into the
response. -/
def addInto (p : PermutationPort) (E : QReg) :
    stateReg X Z (callReg X Z p E) ≃ stateReg X Z (callReg X Z p E) where
  toFun q := (q.1, ((q.2.1.1, q.2.1.2 + q.1), q.2.2))
  invFun q := (q.1, ((q.2.1.1, q.2.1.2 - q.1), q.2.2))
  left_inv q := by simp
  right_inv q := by simp

/-- The copy of the query input, which the contraction `coGate` removes. -/
def copyOut (p : PermutationPort) (E : QReg) : callReg X Z p E → stateReg X Z (callReg X Z p E) :=
  fun r ↦ ((r.1 : (X × Z) × (X × Z)).1, r)

omit [AddCommGroup X] [AddCommGroup Z] in
theorem copyOut_injective (p : PermutationPort) (E : QReg) :
    Function.Injective (copyOut (X := X) (Z := Z) p E) :=
  fun _ _ hab ↦ congrArg Prod.snd hab

/-- **One call of the permutation oracle**, by the three random functions: copy the query input
`s` into a fresh state register, evaluate the port's permutation on it in place, add it into the
response, evaluate the inverse permutation in place, which returns the copy to `s`, and remove
the copy. Six calls: two of each port. -/
noncomputable def simCall (π : Equiv.Perm (X × Z)) (p : PermutationPort) (E : QReg) {A : QReg}
    (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) :
    QuantumComp₂ LocalSig.instruments.{v} (spongeSpec X Z) A (callReg X Z p E) Unit :=
  ((isoGate (copyIn ℓ) (copyIn_injective ℓ)).bind fun _ ↦
    (evalPort (callReg X Z p E) π p).bind fun _ ↦
      (isoGate (addInto p E) (addInto p E).injective).bind fun _ ↦
        evalPort (callReg X Z p E) π (flipPort p)).bind fun _ ↦
    coGate (copyOut p E) (copyOut_injective p E)

/-- The basis map of a call of port `p` of the oracle of `φ`: `|s, y, e⟩ ↦ |s, y + φ s, e⟩`, with
`φ⁻¹` for the inverse port. -/
def callMap (φ : Equiv.Perm (X × Z)) (p : PermutationPort) {A D : QReg}
    (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) : A × D → callReg X Z p E × D :=
  fun q ↦ ((((ℓ q.1).1.1, (ℓ q.1).1.2 + portPerm φ p (ℓ q.1).1.1), (ℓ q.1).2), q.2)

theorem runsAs_evalPort (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z))
    (p : PermutationPort) :
    RunsAs (spongeFnRuntime h k k') (evalPort.{v} F π p)
      (onState (portPerm (spongePerm (h, k, k') π) p)) := by
  cases p
  exacts [runsAs_evalPerm F h k k' π, runsAs_evalPermInv F h k k' π]

/-- **The simulated call runs as the call of `φ`.** -/
theorem runsAs_simCall (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z))
    (p : PermutationPort) {A : QReg} (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) :
    RunsAs (spongeFnRuntime h k k') (simCall.{v} π p E ℓ)
      (callMap (spongePerm (h, k, k') π) p ℓ) := by
  unfold simCall
  refine ((runsAs_isoGate _ _).bind ((runsAs_evalPort _ h k k' π p).bind
    ((runsAs_isoGate _ _).bind (runsAs_evalPort _ h k k' π (flipPort p))))).bind_coGate _ _ _
    fun q ↦ ?_
  simp [onState, copyIn, addInto, copyOut, callMap, portPerm_flipPort_apply]

/-- The permutation oracle's call of port `p` is the basis map `callMap`. -/
theorem branch_queryStep_permutationRuntime (φ : Equiv.Perm (X × Z)) (p : PermutationPort)
    {A : QReg} (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) :
    ((permutationRuntime φ).queryStep p E ℓ).branch () =
      MatrixMap.conj (basisMatrix (callMap φ p ℓ)) := by
  have hstep : ((permutationRuntime φ).step p).branch () =
      MatrixMap.conj (basisMatrix (Prod.map (oracleEquiv (portPerm φ p)) (id : Unit → Unit))) := by
    cases p
    exacts [branch_frame_oracleQuery φ Unit, branch_frame_oracleQuery φ.symm Unit]
  rw [branch_queryStep_of_basis _ _ hstep]
  rfl

/-! ## Substitution -/

variable {L : LocalSig.{u, v}} {W : QReg → Type w}

/-- The tree that replaces a call of port `p` through `ℓ`: `simCall`, ending at the call's
response. -/
noncomputable def simTree (π : Equiv.Perm (X × Z)) (p : PermutationPort) (E : QReg) {A : QReg}
    (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) :
    QuantumComp LocalSig.instruments.{v} (spongeSpec X Z)
      (fun t ↦ Subtype fun _ : ULift.{v} Unit ↦ callReg X Z p E = t) A :=
  QuantumComp.bind (simCall π p E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up (), l.1.symm⟩

/-- The substitution: a local operation becomes the instrument that `I` gives it, and a call
becomes `simTree`. -/
noncomputable def simSubst (I : L.Interp) (π : Equiv.Perm (X × Z)) :
    CommandSubstitution (QuantumComp.toIPFunctor L (qrpmSpec (X × Z)))
      (QuantumComp.toIPFunctor LocalSig.instruments.{v} (spongeSpec X Z))
  | _, .prim o => QuantumComp.primBind (L := LocalSig.instruments.{v})
      ⟨L.Outcome o, fun b ↦ L.next o b, I o⟩ fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query p E ℓ => simTree π p E ℓ

/-- **The simulation of a permutation-oracle program** by the three random functions, given `π`:
every local operation becomes the instrument that `I` gives it, and every call of `φ` or `φ⁻¹`
becomes `simCall`. -/
noncomputable def simulate (I : L.Interp) (π : Equiv.Perm (X × Z)) {A : QReg}
    (x : QuantumComp L (qrpmSpec (X × Z)) W A) :
    QuantumComp LocalSig.instruments.{v} (spongeSpec X Z) W A :=
  IFreeM.substitute (simSubst I π) x

/-! ## Query budget -/

omit [AddCommGroup X] [AddCommGroup Z] in
theorem isQueryBound_isoGate {A B : QReg} (f : A → B) (hf : Function.Injective f)
    (b : SpongePort → ℕ) : (isoGate.{v} (spec := spongeSpec X Z) f hf).IsQueryBound b :=
  fun _ ↦ ⟨Nat.zero_le _, fun _ ↦ trivial⟩

omit [AddCommGroup X] [AddCommGroup Z] in
theorem isQueryBound_coGate {A B : QReg} (f : B → A) (hf : Function.Injective f)
    (b : SpongePort → ℕ) : (coGate.{v} (spec := spongeSpec X Z) f hf).IsQueryBound b :=
  fun _ ↦ ⟨Nat.zero_le _, fun _ ↦ trivial⟩

/-- The budget of one call of the port `j`. -/
def portBudget (j : SpongePort) : SpongePort → ℕ :=
  fun i ↦ if i = j then 1 else 0

omit [AddCommGroup X] [AddCommGroup Z] in
theorem isQueryBound_omegaH :
    (omegaH.{v} (X := X) (Z := Z) F).IsQueryBound (portBudget .h + 0) :=
  QuantumComp₂.isQueryBound_bind
    ((QuantumComp₂.isQueryBound_query_iff _ _ _ _).mpr (by simp [portBudget]))
    fun _ ↦ isQueryBound_isoGate _ _ _

theorem isQueryBound_evalPort (π : Equiv.Perm (X × Z)) (p : PermutationPort) :
    (evalPort.{v} F π p).IsQueryBound fun _ ↦ 1 := by
  have hk := (QuantumComp₂.isQueryBound_query_iff (L := LocalSig.instruments.{v})
    (spec := spongeSpec X Z) (A := stateReg X Z F) .k F (Equiv.refl _) (portBudget .k)).mpr
    (by simp [portBudget])
  have hk' := (QuantumComp₂.isQueryBound_query_iff (L := LocalSig.instruments.{v})
    (spec := spongeSpec X Z) (A := stateReg X Z F) .k' F (Equiv.refl _) (portBudget .k')).mpr
    (by simp [portBudget])
  have hg := fun e : Equiv.Perm (X × Z) ↦ isQueryBound_isoGate (X := X) (Z := Z)
    (A := stateReg X Z F) (B := stateReg X Z F)
    (Prod.map e (id : F → F)) ((Equiv.injective e).prodMap Function.injective_id) 0
  cases p
  · refine (QuantumComp₂.isQueryBound_bind hk fun _ ↦ QuantumComp₂.isQueryBound_bind (hg π)
      fun _ ↦ QuantumComp₂.isQueryBound_bind hk' fun _ ↦ isQueryBound_omegaH F).mono ?_
    intro i
    cases i <;> simp [portBudget]
  · refine (QuantumComp₂.isQueryBound_bind (QuantumComp₂.isQueryBound_bind (hg _) fun _ ↦
      QuantumComp₂.isQueryBound_bind (isQueryBound_omegaH F) fun _ ↦ hg _) fun _ ↦
      QuantumComp₂.isQueryBound_bind (QuantumComp₂.isQueryBound_bind (hg _) fun _ ↦
        QuantumComp₂.isQueryBound_bind hk' fun _ ↦ hg _) fun _ ↦
      QuantumComp₂.isQueryBound_bind (hg π⁻¹) fun _ ↦
        QuantumComp₂.isQueryBound_bind (hg _) fun _ ↦
          QuantumComp₂.isQueryBound_bind hk fun _ ↦ hg _).mono ?_
    intro i
    cases i <;> simp [portBudget]

/-- A simulated call makes two calls of each port. -/
theorem isQueryBound_simCall (π : Equiv.Perm (X × Z)) (p : PermutationPort) {A : QReg}
    (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) :
    (simCall.{v} π p E ℓ).IsQueryBound fun _ ↦ 2 := by
  refine (QuantumComp₂.isQueryBound_bind (QuantumComp₂.isQueryBound_bind
    (isQueryBound_isoGate _ _ 0) fun _ ↦ QuantumComp₂.isQueryBound_bind
      (isQueryBound_evalPort _ π p) fun _ ↦ QuantumComp₂.isQueryBound_bind
        (isQueryBound_isoGate _ _ 0) fun _ ↦ isQueryBound_evalPort _ π (flipPort p))
    fun _ ↦ isQueryBound_coGate _ _ 0).mono ?_
  intro i
  simp

/-- **Query budget.** If every path of `x` makes at most `q` calls of `φ` and `φ⁻¹` together,
every path of the simulation calls each of `h`, `k`, `k'` at most `2 * q` times. -/
theorem isQueryBound_simulate (I : L.Interp) (π : Equiv.Perm (X × Z)) {A : QReg}
    {x : QuantumComp L (qrpmSpec (X × Z)) W A} {q : ℕ} (hx : x.IsTotalQueryBound q) :
    (simulate I π x).IsQueryBound fun _ ↦ 2 * q := by
  intro j
  refine IFreeM.IsChargeBound.substitute_mul (simSubst I π) 2 (fun B c ↦ ?_) hx
  cases c with
  | prim o =>
    exact (QuantumComp.isQueryBoundAt_primBind_iff (L := LocalSig.instruments.{v}) _ _ j _).mpr
      fun _ ↦ trivial
  | query p E ℓ =>
    show (simTree π p E ℓ).IsQueryBoundAt j (2 + 0)
    exact QuantumComp.IsQueryBoundAt.bind (isQueryBound_simCall π p ℓ j) fun _ _ ↦ trivial

/-! ## Semantics -/

/-- Running a fixed-register program with unit value followed by a continuation runs the program,
then the continuation at its unique leaf. -/
theorem branch_run_bind_unit {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)
    {L' : LocalSig.{u, v}} (I : L'.Interp) {Y : QReg → Type w} {A B : QReg}
    (x : QuantumComp L' spec (QuantumComp₂.Leaf B Unit) A)
    (g : ∀ u, QuantumComp₂.Leaf B Unit u → QuantumComp L' spec Y u) (q : Σ u, Y u) :
    (R.run I (x.bind g)).branch q =
      (R.run I (g B ⟨rfl, ()⟩)).branch q ∘ₗ (R.run₂ I x).branch () := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply,
    ← (QuantumComp₂.leafEquiv B Unit).tsum_eq, tsum_fintype, Fintype.sum_unique]
  rfl

theorem branch_run_simTree_bind (R : QuantumRuntime (spongeSpec X Z)) (π : Equiv.Perm (X × Z))
    (p : PermutationPort) {A : QReg} (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E)
    (g : ∀ t, (Subtype fun _ : ULift.{v} Unit ↦ callReg X Z p E = t) →
      QuantumComp LocalSig.instruments.{v} (spongeSpec X Z) W t) (q : Σ u, W u) :
    (R.run .instruments ((simTree π p E ℓ).bind g)).branch q =
      (R.run .instruments (g _ ⟨ULift.up (), rfl⟩)).branch q ∘ₗ
        (R.run₂ .instruments (simCall.{v} π p E ℓ)).branch () :=
  (congrArg (fun y ↦ (R.run .instruments y).branch q)
    (QuantumComp.bind_assoc (simCall π p E ℓ) _ g)).trans
    (branch_run_bind_unit R .instruments _ _ q)

/-- **The simulation runs as the permutation oracle.** Against the oracles of `(h, k, k')`, the
simulation of `x` given `π` runs to the same dependent subinstrument as `x` against
`spongePerm (h, k, k') π`. -/
theorem run_simulate (I : L.Interp) (π : Equiv.Perm (X × Z)) (t : SpongeKeys X Z) {A : QReg}
    (x : QuantumComp L (qrpmSpec (X × Z)) W A) :
    (spongeFnRuntime t.1 t.2.1 t.2.2).run .instruments (simulate I π x) =
      (permutationRuntime (spongePerm t π)).run I x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    rw [QuantumRuntime.run_primBind]
    exact congrArg (((I o).frame _).bind) (funext ih)
  | queryBind _ p E ℓ k ih =>
    refine DSubInstrument.ext (funext fun q ↦ ?_)
    refine (branch_run_simTree_bind _ π p ℓ _ q).trans ?_
    have hs := runsAs_simCall.{v} t.1 t.2.1 t.2.2 π p ℓ
    rw [RunsAs] at hs
    rw [hs, QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_unit,
      branch_queryStep_permutationRuntime, ← ih ()]
    rfl

/-- The simulation is observed as the original program against `φ`. -/
theorem evalDistMap_simulate {β : Type*} [MeasurableSpace β] (I : L.Interp)
    (π : Equiv.Perm (X × Z)) (t : SpongeKeys X Z) {A : QReg}
    (x : QuantumComp L (qrpmSpec (X × Z)) W A) (ρ : SubState A) (f : (Σ u, W u) → β) :
    (spongeFnRuntime t.1 t.2.1 t.2.2).evalDistMap .instruments (simulate I π x) ρ f =
      (permutationRuntime (spongePerm t π)).evalDistMap I x ρ f := by
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.jointPost, run_simulate]
  rfl

/-- The simulation of a lossless program runs losslessly. -/
theorem lossless_run_simulate (I : L.Interp) (π : Equiv.Perm (X × Z)) (t : SpongeKeys X Z)
    {A : QReg} {x : QuantumComp L (qrpmSpec (X × Z)) W A} (hx : x.Lossless I) :
    ((spongeFnRuntime t.1 t.2.1 t.2.2).run .instruments (simulate I π x)).Lossless := by
  rw [run_simulate]
  exact (permutationRuntime _).lossless_run I hx (lossless_permutationRuntime_step _)

/-- **The reduction.** The quantum random-permutation model is the average over `π` of the
experiment against uniform `(h, k, k')` of the simulation, observed through `φ = spongePerm t π`
and the leaf. -/
theorem qrpmEvalDistMap_eq_simulate {β : Type*} [MeasurableSpace β] (I : L.Interp) {A : QReg}
    (x : QuantumComp L (qrpmSpec (X × Z)) W A) (ρ : SubState A)
    (f : Equiv.Perm (X × Z) → (Σ u, W u) → β) :
    qrpmEvalDistMap I x ρ f =
      (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ •
        ∑ π, spongeEvalDistMap .instruments (simulate I π x) ρ fun t ↦ f (spongePerm t π) := by
  rw [← qrpmEvalDistMap_eq_spongePerm, sampledEvalDistMap_eq_sum, Fintype.sum_prod_type,
    Finset.sum_comm, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    mul_comm, ← smul_smul, Finset.smul_sum]
  simp only [spongeEvalDistMap_eq_sum, evalDistMap_simulate]

/-- The reduction for observations of the leaf alone. -/
theorem qrpmEvalDistMap_eq_simulate_leaf {β : Type*} [MeasurableSpace β] (I : L.Interp)
    {A : QReg} (x : QuantumComp L (qrpmSpec (X × Z)) W A) (ρ : SubState A)
    (f : (Σ u, W u) → β) :
    qrpmEvalDistMap I x ρ (fun _ ↦ f) =
      (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ •
        ∑ π, spongeEvalDistMap .instruments (simulate I π x) ρ fun _ ↦ f :=
  qrpmEvalDistMap_eq_simulate I x ρ fun _ ↦ f

end Quantum.Sponge

end
