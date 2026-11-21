module

public import Quantum.Par.Spec
public import Quantum.Sponge.Simulate

@[expose] public section

/-!
# The lockstep simulation of a round of permutation calls

A round of `w` calls of the permutation oracle, simulated slot by slot (`simulate` of
`Quantum.Par.seqCalls`), makes `6 w` sequential calls of the sponge's random functions. In both
directions the two calls of `h` of a slot are separated only by local gates and calls of `k`,
`k'`, so the `w` slots can be run in lockstep (`lockRound`): every slot's calls before its first
`h` call, one round of `w` calls of `h`, every slot's calls between its two `h` calls, a second
round of `h`, the remaining calls. The two programs have the same run against every runtime whose
sponge ports, in a basis given by a unitary `U` of its register, add functions read off the basis
state (`IsReadRuntime`): compressed and hardwired runtimes, and the oracles of fixed functions.

* **Read runtimes** (`readRuntime`): the ports add the functions `rd s` of the basis state `s`
  and keep `s`. The building blocks of `simCall` run as basis maps against them (as in
  `Quantum.Sponge.Simulate` for fixed functions), so `simulate` runs as the permutation oracle
  that reads `spongePerm (rd s) π` (`run_simulate_read`).
* **Rounds of basis steps** (`roundKraus_basis`, `branch_run₂_seqCalls_basis`): a round of steps
  that are basis maps keeping the runtime register is the basis map of all calls at once.
* **The lockstep round** (`lockRound`) runs as the same basis map
  (`runsAs_lockRound_read`), hence `branch_run₂_simulate_seqCalls_eq_lockRound` for every read
  runtime, by the simulation through `U`.
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker

universe u

namespace Quantum.Par

open Quantum Quantum.Sponge QuantumRuntime SubInstrument

/-! ## Rounds of basis steps -/

section basis

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)
  (G : ∀ p, R.D → spec.In p → spec.Out p)

/-- The basis map of a step that maps the input by `G p s` at the runtime state `s`. -/
def stepMap (p : spec.Port) : spec.In p × R.D → spec.Out p × R.D :=
  fun q ↦ (G p q.2 q.1, q.2)

/-- **A round of basis steps** is the basis map of all its calls at once. -/
theorem roundKraus_basis :
    ∀ {w : ℕ} (f : Fin w → spec.Port) (rs : RoundResult spec f),
      R.roundKraus (fun p _ ↦ basisMatrix (stepMap R G p)) f rs =
        basisMatrix (fun q : roundIn spec f × R.D ↦
          ((fun i ↦ G (f i) q.2 (q.1 i) : ∀ i, spec.Out (f i)), q.2))
  | 0, f, rs => by
    simp only [QuantumRuntime.roundKraus]
    congr 1
    funext q
    exact Prod.ext (funext fun i ↦ i.elim0) rfl
  | w + 1, f, rs => by
    simp only [QuantumRuntime.roundKraus]
    rw [roundKraus_basis (fun i ↦ f i.succ) (Fin.tail rs), basisMatrix_kronecker_one,
      basisMatrix_kronecker_one, ← basisMatrix_comp, ← basisMatrix_comp, ← basisMatrix_comp,
      ← basisMatrix_comp]
    congr 1
    funext q
    refine Prod.ext (funext fun i ↦ ?_) rfl
    cases i using Fin.cases <;> rfl

variable {R G}

/-- **The step of a round of basis steps.** -/
theorem branch_roundStep_basis
    (hG : ∀ p r, (R.step p).branch r = MatrixMap.conj (basisMatrix (stepMap R G p))) {w : ℕ}
    (f : Fin w → spec.Port) (rs : RoundResult spec f) :
    (R.roundStep f).branch rs = MatrixMap.conj (basisMatrix (fun q : roundIn spec f × R.D ↦
      ((fun i ↦ G (f i) q.2 (q.1 i) : ∀ i, spec.Out (f i)), q.2))) := by
  rw [R.branch_roundStep_of_conj (fun p _ ↦ basisMatrix (stepMap R G p)) hG f rs,
    roundKraus_basis]

/-- Three basis maps in a row. -/
theorem conj_basisMatrix_comp₃ {A B C D' : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype D'] [DecidableEq B] [DecidableEq C] [DecidableEq D'] (h : C → D') (g : B → C)
    (f : A → B) (ρ : Matrix A A ℂ) :
    MatrixMap.conj (basisMatrix h) (MatrixMap.conj (basisMatrix g) (MatrixMap.conj
      (basisMatrix f) ρ)) = MatrixMap.conj (basisMatrix (h ∘ g ∘ f)) ρ := by
  rw [basisMatrix_comp, basisMatrix_comp, MatrixMap.conj_mul, MatrixMap.conj_mul]
  rfl

/-- **The calls of a round, against basis steps**: the basis map of all calls at once. -/
theorem branch_run₂_seqCalls_basis
    (hG : ∀ p r, (R.step p).branch r = MatrixMap.conj (basisMatrix (stepMap R G p))) {w : ℕ}
    (f : Fin w → spec.Port) (E : QReg) {A B : QReg} (ℓ : A ≃ roundIn spec f × E)
    (post : roundOut spec f × E ≃ B) (rs : RoundResult spec f) :
    (R.run₂ .instruments (seqCalls f E ℓ post)).branch rs =
      MatrixMap.conj (basisMatrix (fun q : A × R.D ↦
        (post ((fun i ↦ G (f i) q.2 ((ℓ q.1).1 i) : ∀ i, spec.Out (f i)), (ℓ q.1).2), q.2))) := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [R.run₂_seqCalls, DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
    DSubInstrument.branch_bind_apply, tsum_eq_single rs fun rs' h ↦ ?_]
  · rw [DSubInstrument.branch_bind_unit, SubInstrument.branch_pure_self, LinearMap.id_comp,
      DSubInstrument.branch_frame_apply, branch_roundStep_basis hG, MatrixMap.amplify_conj,
      basisMatrix_kronecker_one, branch_relabel, branch_relabel, conj_basisMatrix_comp₃]
    rfl
  · rw [DSubInstrument.branch_bind_unit, SubInstrument.branch_pure_of_ne (Ne.symm h),
      LinearMap.zero_comp,
      LinearMap.zero_apply]

end basis

/-! ## Programs that run as basis maps, over any signature -/

section runsAs

variable {spec : QuantumOracleSpec.{0, 0}} {R : QuantumRuntime spec}

/-- A call with a single result, then a continuation, runs as the call's basis map, then the
continuation's. -/
theorem RunsAs.queryBind {i : spec.Port} [Unique (spec.Result i)]
    (g : spec.In i × R.D → spec.Out i × R.D)
    (hg : ∀ r, (R.step i).branch r = MatrixMap.conj (basisMatrix g)) (E : QReg) {A C : QReg}
    (ℓ : A ≃ spec.In i × E)
    {y : spec.Result i → QuantumComp₂ LocalSig.instruments.{0} spec (QReg.of (spec.Out i × E))
      C Unit}
    {F : (spec.Out i × E) × R.D → C × R.D} (hy : ∀ r, RunsAs R (y r) F) :
    RunsAs R (QuantumComp₂.queryBind i E ℓ y)
      (F ∘ QuantumRuntime.queryEquivOut (spec.Out i) R.D E ∘ Prod.map g id ∘
        QuantumRuntime.queryEquivIn ℓ R.D) := by
  unfold RunsAs
  refine LinearMap.ext fun ρ ↦ ?_
  have hy' := hy default
  unfold RunsAs at hy'
  rw [QuantumRuntime.run₂_queryBind, DSubInstrument.branch_bind_apply, tsum_fintype,
    Fintype.sum_unique, hy', branch_queryStep_of_basis R g (hg default) E ℓ,
    ← LinearMap.comp_apply, ← MatrixMap.conj_mul, ← basisMatrix_comp]

/-- `pure ()` runs as the identity. -/
theorem runsAs_pure {A : QReg} :
    RunsAs R (QuantumComp₂.pure () : QuantumComp₂ LocalSig.instruments.{0} spec A A Unit) id := by
  rw [RunsAs, QuantumRuntime.run₂_pure, SubInstrument.branch_pure_self, basisMatrix_id,
    MatrixMap.conj_one]

end runsAs

/-! ## Read runtimes -/

section read

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z]

/-- The oracle of port `p` of the functions `t` on its register. -/
def spongeKeyEquiv (t : SpongeKeys X Z) : (p : SpongePort) → (spongeIn X Z p ≃ spongeIn X Z p)
  | .h => oracleEquiv t.1
  | .k => oracleEquiv t.2.1
  | .k' => oracleEquiv t.2.2

variable {D : QReg}

/-- A port that adds the functions read off the basis state of the register. -/
def readEquiv (rd : D → SpongeKeys X Z) (p : SpongePort) :
    spongeIn X Z p × D ≃ spongeIn X Z p × D where
  toFun q := (spongeKeyEquiv (rd q.2) p q.1, q.2)
  invFun q := ((spongeKeyEquiv (rd q.2) p).symm q.1, q.2)
  left_inv q := by simp
  right_inv q := by simp

variable (D) in
/-- **A read runtime**: each port adds the functions `rd s` read off the basis state `s` of the
register, which it keeps. -/
noncomputable def readRuntime (σ₀ : SubState D) (rd : D → SpongeKeys X Z) :
    QuantumRuntime (spongeSpec X Z) where
  D := D
  init := σ₀
  step p := relabel (readEquiv rd p)

variable {σ₀ : SubState D} {rd : D → SpongeKeys X Z}

theorem readRuntime_branch (p : SpongePort) (r : Unit) :
    ((readRuntime D σ₀ rd).step p).branch r = MatrixMap.conj (basisMatrix
      (stepMap (readRuntime D σ₀ rd) (fun p s ↦ spongeKeyEquiv (rd s) p) p)) :=
  branch_relabel _ r

/-- **A runtime that reads its functions off its register**, in the basis given by the unitary
`U`: every port is `(1 ⊗ Uᴴ) T (1 ⊗ U)` with `T` the port of the read runtime. -/
def IsReadRuntime (R : QuantumRuntime (spongeSpec X Z)) (U : Matrix R.D R.D ℂ)
    (rd : R.D → SpongeKeys X Z) : Prop :=
  ∀ p, (R.step p).branch () = MatrixMap.conj
    (((1 : Matrix (spongeIn X Z p) (spongeIn X Z p) ℂ) ⊗ₖ Uᴴ) * basisMatrix (readEquiv rd p) *
      ((1 : Matrix (spongeIn X Z p) (spongeIn X Z p) ℂ) ⊗ₖ U))

/-- The state register of an in-place evaluation, with the permutation `e s` at the runtime
state `s`. -/
def onStateD {F : Type*} (e : D → Equiv.Perm (X × Z)) :
    ((X × Z) × F) × D → ((X × Z) × F) × D :=
  fun q ↦ ((e q.2 q.1.1, q.1.2), q.2)

variable (F : QReg) (σ₀ rd)

theorem runsAs_stateGate_read (e : Equiv.Perm (X × Z)) :
    RunsAs (readRuntime D σ₀ rd) (stateGate.{0} F e) (onStateD fun _ ↦ e) :=
  (runsAs_isoGate _ _).congr fun _ ↦ rfl

theorem runsAs_sigmaK_read :
    RunsAs (readRuntime D σ₀ rd) (sigmaK.{0} F) (onStateD fun s ↦ capacityRound (rd s).2.1) := by
  unfold sigmaK
  exact (runsAs_query _ .k _ (readRuntime_branch .k ()) F _).congr fun _ ↦ rfl

theorem runsAs_sigmaK'_read :
    RunsAs (readRuntime D σ₀ rd) (sigmaK'.{0} F) (onStateD fun s ↦ capacityRound (rd s).2.2) := by
  unfold sigmaK'
  exact (runsAs_query _ .k' _ (readRuntime_branch .k' ()) F _).congr fun _ ↦ rfl

theorem runsAs_omegaH_read :
    RunsAs (readRuntime D σ₀ rd) (omegaH.{0} F) (onStateD fun s ↦ rateRound (rd s).1) := by
  unfold omegaH
  exact ((runsAs_query _ .h _ (readRuntime_branch .h ()) F _).bind
    (runsAs_isoGate _ _)).congr fun _ ↦ rfl

theorem runsAs_sigmaKInv_read :
    RunsAs (readRuntime D σ₀ rd) (sigmaKInv.{0} F)
      (onStateD fun s ↦ (capacityRound (rd s).2.1)⁻¹) := by
  unfold sigmaKInv
  exact ((runsAs_stateGate_read σ₀ rd F _).bind ((runsAs_sigmaK_read σ₀ rd F).bind
    (runsAs_stateGate_read σ₀ rd F _))).congr fun q ↦ by
      simp [onStateD, negCap, capacityRound_inv_apply, sub_eq_add_neg, add_comm]

theorem runsAs_sigmaK'Inv_read :
    RunsAs (readRuntime D σ₀ rd) (sigmaK'Inv.{0} F)
      (onStateD fun s ↦ (capacityRound (rd s).2.2)⁻¹) := by
  unfold sigmaK'Inv
  exact ((runsAs_stateGate_read σ₀ rd F _).bind ((runsAs_sigmaK'_read σ₀ rd F).bind
    (runsAs_stateGate_read σ₀ rd F _))).congr fun q ↦ by
      simp [onStateD, negCap, capacityRound_inv_apply, sub_eq_add_neg, add_comm]

theorem runsAs_omegaHInv_read :
    RunsAs (readRuntime D σ₀ rd) (omegaHInv.{0} F)
      (onStateD fun s ↦ (rateRound (rd s).1)⁻¹) := by
  unfold omegaHInv
  exact ((runsAs_stateGate_read σ₀ rd F _).bind ((runsAs_omegaH_read σ₀ rd F).bind
    (runsAs_stateGate_read σ₀ rd F _))).congr fun q ↦ by
      simp [onStateD, negRate, rateRound_inv_apply, sub_eq_add_neg, add_comm]

theorem runsAs_evalPerm_read (π : Equiv.Perm (X × Z)) :
    RunsAs (readRuntime D σ₀ rd) (evalPerm.{0} F π)
      (onStateD fun s ↦ spongePerm (rd s) π) := by
  unfold evalPerm
  exact ((runsAs_sigmaK_read σ₀ rd F).bind ((runsAs_stateGate_read σ₀ rd F π).bind
    ((runsAs_sigmaK'_read σ₀ rd F).bind (runsAs_omegaH_read σ₀ rd F)))).congr fun _ ↦ rfl

theorem runsAs_evalPermInv_read (π : Equiv.Perm (X × Z)) :
    RunsAs (readRuntime D σ₀ rd) (evalPermInv.{0} F π)
      (onStateD fun s ↦ (spongePerm (rd s) π)⁻¹) := by
  unfold evalPermInv
  refine ((runsAs_omegaHInv_read σ₀ rd F).bind ((runsAs_sigmaK'Inv_read σ₀ rd F).bind
    ((runsAs_stateGate_read σ₀ rd F π⁻¹).bind (runsAs_sigmaKInv_read σ₀ rd F)))).congr
    fun q ↦ ?_
  simp only [onStateD, Function.comp_apply, spongePerm, _root_.mul_inv_rev, Equiv.Perm.mul_apply]

theorem runsAs_evalPort_read (π : Equiv.Perm (X × Z)) (p : PermutationPort) :
    RunsAs (readRuntime D σ₀ rd) (evalPort.{0} F π p)
      (onStateD fun s ↦ portPerm (spongePerm (rd s) π) p) := by
  cases p
  exacts [runsAs_evalPerm_read σ₀ rd F π, runsAs_evalPermInv_read σ₀ rd F π]

variable {E : QReg}

/-- **The simulated call reads its permutation off the register.** -/
theorem runsAs_simCall_read (π : Equiv.Perm (X × Z)) (p : PermutationPort) {A : QReg}
    (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) :
    RunsAs (readRuntime D σ₀ rd) (simCall.{0} π p E ℓ)
      (fun q ↦ callMap (spongePerm (rd q.2) π) p ℓ q) := by
  unfold simCall
  refine ((runsAs_isoGate _ _).bind ((runsAs_evalPort_read σ₀ rd _ π p).bind
    ((runsAs_isoGate _ _).bind (runsAs_evalPort_read σ₀ rd _ π (flipPort p))))).bind_coGate
    _ _ _
    fun q ↦ ?_
  simp [onStateD, copyIn, addInto, copyOut, callMap, portPerm_flipPort_apply]

/-- The permutation oracle that reads `spongePerm (rd s) π` off the register. -/
def permReadEquiv (π : Equiv.Perm (X × Z)) (rd : D → SpongeKeys X Z) (p : PermutationPort) :
    (qrpmSpec (X × Z)).In p × D ≃ (qrpmSpec (X × Z)).Out p × D where
  toFun q := (oracleEquiv (portPerm (spongePerm (rd q.2) π) p) q.1, q.2)
  invFun q := ((oracleEquiv (portPerm (spongePerm (rd q.2) π) p)).symm q.1, q.2)
  left_inv q := by simp
  right_inv q := by simp

variable (D) in
/-- **The permutation oracle of a read runtime.** -/
noncomputable def permReadRuntime (σ₀ : SubState D) (π : Equiv.Perm (X × Z))
    (rd : D → SpongeKeys X Z) : QuantumRuntime (qrpmSpec (X × Z)) where
  D := D
  init := σ₀
  step p := relabel (permReadEquiv π rd p)

theorem permReadRuntime_branch (π : Equiv.Perm (X × Z)) (p : PermutationPort) (r : Unit) :
    ((permReadRuntime D σ₀ π rd).step p).branch r = MatrixMap.conj (basisMatrix
      (stepMap (permReadRuntime D σ₀ π rd)
        (fun p s ↦ oracleEquiv (portPerm (spongePerm (rd s) π) p)) p)) :=
  branch_relabel _ r

theorem branch_queryStep_permReadRuntime (π : Equiv.Perm (X × Z)) (p : PermutationPort)
    {A : QReg} (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) :
    ((permReadRuntime D σ₀ π rd).queryStep p E ℓ).branch () =
      MatrixMap.conj (basisMatrix (fun q ↦ callMap (spongePerm (rd q.2) π) p ℓ q)) := by
  rw [branch_queryStep_of_basis _ _ (permReadRuntime_branch σ₀ rd π p ())]
  rfl

/-- **The simulation runs as the permutation oracle read off the register.** -/
theorem run_simulate_read {L : LocalSig.{u, 0}} {W : QReg → Type} (I : L.Interp)
    (π : Equiv.Perm (X × Z)) {A : QReg} (x : QuantumComp L (qrpmSpec (X × Z)) W A) :
    (readRuntime D σ₀ rd).run .instruments (simulate I π x) =
      (permReadRuntime D σ₀ π rd).run I x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    rw [QuantumRuntime.run_primBind]
    exact congrArg (((I o).frame _).bind) (funext ih)
  | queryBind _ p E ℓ k ih =>
    refine DSubInstrument.ext (funext fun q ↦ ?_)
    refine (branch_run_simTree_bind _ π p ℓ _ q).trans ?_
    have hs := runsAs_simCall_read σ₀ rd π p ℓ
    rw [RunsAs] at hs
    rw [hs, QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_unit,
      branch_queryStep_permReadRuntime, ← ih ()]
    rfl

end read

/-! ## The lockstep round -/

section lock

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z]

/-- The port of the rounds of the lockstep simulation: `h`. -/
abbrev spongeHPort : Unit → SpongePort := fun _ ↦ .h

variable (X Z) in
/-- The signature of the lockstep simulation: single calls of `h`, `k`, `k'` and rounds of `h`. -/
abbrev lockSpec : QuantumOracleSpec.{0, 0} := parSpec (spongeSpec X Z) spongeHPort

variable (X Z) in
/-- The register of a slot: the state of the in-place evaluation, then the call's input and
response. -/
abbrev SlotT : Type := (X × Z) × ((X × Z) × (X × Z))

variable {w : ℕ} {E : QReg}

/-- Decidable equality of the slots, named so that instance search stays small. -/
instance instDecidableEqSlots : DecidableEq (Fin w → SlotT X Z) := inferInstance

/-- Decidable equality of the other slots. -/
instance instDecidableEqSlotsNe (j : Fin w) : DecidableEq ({i // i ≠ j} → SlotT X Z) :=
  inferInstance

/-- Decidable equality of the call registers of the slots. -/
instance instDecidableEqSlotCalls : DecidableEq (Fin w → (X × Z) × (X × Z)) := inferInstance

variable (X Z w E) in
/-- The register of a round in lockstep: the slots, beside the remainder. -/
abbrev lockReg : QReg := QReg.of ((Fin w → SlotT X Z) × E)

variable (X Z) in
/-- The rest of the lockstep register beside the state of slot `j`. -/
abbrev slotRest (j : Fin w) (E : QReg) : QReg :=
  QReg.of ((((X × Z) × (X × Z)) × ({i // i ≠ j} → SlotT X Z)) × E)

/-- The state of slot `j`, split off the lockstep register. -/
def slotSplit (j : Fin w) :
    (Fin w → SlotT X Z) × E ≃ (X × Z) × ((((X × Z) × (X × Z)) × ({i // i ≠ j} → SlotT X Z)) × E)
    where
  toFun x := ((x.1 j).1, (((x.1 j).2, fun i ↦ x.1 i.1), x.2))
  invFun y := (fun i ↦ if h : i = j then (y.1, y.2.1.1) else y.2.1.2 ⟨i, h⟩, y.2.2)
  left_inv x := by
    refine Prod.ext (funext fun i ↦ ?_) rfl
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  right_inv y := by
    refine Prod.ext (by simp) (Prod.ext (Prod.ext (by simp) (funext fun i ↦ ?_)) rfl)
    simp [i.2]

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
theorem slotSplit_apply (j : Fin w) (x : (Fin w → SlotT X Z) × E) :
    slotSplit j x = ((x.1 j).1, (((x.1 j).2, fun i ↦ x.1 i.1), x.2)) :=
  rfl

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
theorem slotSplit_symm_apply (j : Fin w)
    (y : (X × Z) × ((((X × Z) × (X × Z)) × ({i // i ≠ j} → SlotT X Z)) × E)) :
    (slotSplit j).symm y =
      (fun i ↦ if h : i = j then (y.1, y.2.1.1) else y.2.1.2 ⟨i, h⟩, y.2.2) :=
  rfl

/-- The update of slot `j` by a permutation of its register. -/
def updEquiv (j : Fin w) (g : Equiv.Perm (SlotT X Z)) : Equiv.Perm (Fin w → SlotT X Z) where
  toFun v := Function.update v j (g (v j))
  invFun v := Function.update v j (g.symm (v j))
  left_inv v := by
    funext i
    by_cases h : i = j
    · subst h
      simp
    · simp [Function.update_of_ne h]
  right_inv v := by
    funext i
    by_cases h : i = j
    · subst h
      simp
    · simp [Function.update_of_ne h]

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
theorem updEquiv_apply (j : Fin w) (g : Equiv.Perm (SlotT X Z)) (v : Fin w → SlotT X Z) :
    updEquiv j g v = Function.update v j (g (v j)) :=
  rfl

/-- The local gate of a permutation of the register of slot `j`. -/
noncomputable def gateAt (j : Fin w) (g : Equiv.Perm (SlotT X Z)) :
    QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit :=
  isoGate (Prod.map (updEquiv j g) (id : E → E))
    ((updEquiv j g).injective.prodMap Function.injective_id)

/-- A call of port `p` (`k` or `k'`, through `e`) on the state of slot `j`. -/
noncomputable def capAt (j : Fin w) (p : SpongePort) (e : (X × Z) ≃ spongeIn X Z p) :
    QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit :=
  QuantumComp₂.queryBind (spec := lockSpec X Z) (.inl p) (slotRest X Z j E)
    ((slotSplit j).trans (e.prodCongr (Equiv.refl _))) fun _ ↦
      isoGate (fun y : spongeIn X Z p × slotRest X Z j E ↦ (slotSplit j).symm (e.symm y.1, y.2))
        fun a b h ↦ by
          have h' := (slotSplit j).symm.injective h
          exact Prod.ext (e.symm.injective (Prod.ext_iff.1 h').1) (Prod.ext_iff.1 h').2

variable (X Z w E) in
/-- The rest of the lockstep register beside the states of all slots. -/
abbrev roundRest : QReg := QReg.of ((Fin w → (X × Z) × (X × Z)) × E)

/-- The states of all slots, as inputs of `h` (through the swap), split off the register. -/
def roundSplit' :
    (Fin w → SlotT X Z) × E ≃ (Fin w → Z × X) × ((Fin w → (X × Z) × (X × Z)) × E) where
  toFun x := (fun i ↦ ((x.1 i).1.2, (x.1 i).1.1), (fun i ↦ (x.1 i).2, x.2))
  invFun y := (fun i ↦ (((y.1 i).2, (y.1 i).1), y.2.1 i), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A round of `h`** on the states of all slots. -/
noncomputable def roundAll :
    QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit :=
  QuantumComp₂.queryBind (spec := lockSpec X Z) (.inr (.round w fun _ ↦ ())) (roundRest X Z w E)
    roundSplit' fun _ ↦
      isoGate (fun y : (Fin w → Z × X) × roundRest X Z w E ↦ roundSplit'.symm y)
        roundSplit'.symm.injective

/-- Slot programs in the order of a list of slots. -/
noncomputable def forSlots
    (P : Fin w → QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit) :
    List (Fin w) → QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit
  | [] => QuantumComp₂.pure ()
  | j :: l => (P j).bind fun _ ↦ forSlots P l

/-- A permutation of the state of a slot. -/
def stateE (e : Equiv.Perm (X × Z)) : Equiv.Perm (SlotT X Z) :=
  e.prodCongr (Equiv.refl _)

/-- Adding the state of a slot into its response. -/
def addT : Equiv.Perm (SlotT X Z) where
  toFun t := (t.1, (t.2.1, t.2.2 + t.1))
  invFun t := (t.1, (t.2.1, t.2.2 - t.1))
  left_inv t := by simp
  right_inv t := by simp

/-- `σ_k` on slot `j`. -/
noncomputable abbrev kAt (j : Fin w) :
    QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit :=
  capAt j .k (Equiv.refl _)

/-- `σ_k'` on slot `j`. -/
noncomputable abbrev k'At (j : Fin w) :
    QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit :=
  capAt j .k' (Equiv.refl _)

/-- `σ_k⁻¹` on slot `j`. -/
noncomputable def kInvAt (j : Fin w) :
    QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit :=
  (gateAt j (stateE (negCap X Z))).bind fun _ ↦ (kAt j).bind fun _ ↦
    gateAt j (stateE (negCap X Z))

/-- `σ_k'⁻¹` on slot `j`. -/
noncomputable def k'InvAt (j : Fin w) :
    QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit :=
  (gateAt j (stateE (negCap X Z))).bind fun _ ↦ (k'At j).bind fun _ ↦
    gateAt j (stateE (negCap X Z))

variable (π : Equiv.Perm (X × Z))

/-- The calls of slot `j`, a call of port `p`, before its first call of `h`. -/
noncomputable def phaseA (p : PermutationPort) (j : Fin w) :
    QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit :=
  match p with
  | .forward => (kAt j).bind fun _ ↦ (gateAt j (stateE π)).bind fun _ ↦ k'At j
  | .inverse => gateAt j (stateE (negRate X Z))

/-- The calls of slot `j` between its two calls of `h`. -/
noncomputable def phaseC (p : PermutationPort) (j : Fin w) :
    QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit :=
  match p with
  | .forward => (gateAt j addT).bind fun _ ↦ gateAt j (stateE (negRate X Z))
  | .inverse => (gateAt j (stateE (negRate X Z))).bind fun _ ↦ (k'InvAt j).bind fun _ ↦
      (gateAt j (stateE π⁻¹)).bind fun _ ↦ (kInvAt j).bind fun _ ↦ (gateAt j addT).bind fun _ ↦
        (kAt j).bind fun _ ↦ (gateAt j (stateE π)).bind fun _ ↦ k'At j

/-- The calls of slot `j` after its second call of `h`. -/
noncomputable def phaseE (p : PermutationPort) (j : Fin w) :
    QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit :=
  match p with
  | .forward => (gateAt j (stateE (negRate X Z))).bind fun _ ↦ (k'InvAt j).bind fun _ ↦
      (gateAt j (stateE π⁻¹)).bind fun _ ↦ kInvAt j
  | .inverse => QuantumComp₂.pure ()

variable (dir : Fin w → PermutationPort)

/-- Copy the query input of every slot into its state. -/
def copyAll {A : QReg} (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E) :
    A → (Fin w → SlotT X Z) × E :=
  fun a ↦ (fun i ↦ ((((ℓ a).1 i : (X × Z) × (X × Z))).1, (ℓ a).1 i), (ℓ a).2)

omit [AddCommGroup X] [AddCommGroup Z] in
theorem copyAll_injective {A : QReg} (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E) :
    Function.Injective (copyAll dir ℓ) := fun _ _ h ↦
  ℓ.injective (Prod.ext (funext fun i ↦ (Prod.ext_iff.1 (congrFun (Prod.ext_iff.1 h).1 i)).2)
    (Prod.ext_iff.1 h).2)

/-- The copies of the query inputs, which the last contraction removes. -/
def uncopyAll {B : QReg} (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B) :
    B → (Fin w → SlotT X Z) × E :=
  fun b ↦ (fun i ↦ ((((post.symm b).1 i : (X × Z) × (X × Z))).1, (post.symm b).1 i),
    (post.symm b).2)

omit [AddCommGroup X] [AddCommGroup Z] in
theorem uncopyAll_injective {B : QReg} (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B) :
    Function.Injective (uncopyAll dir post) := fun _ _ h ↦
  post.symm.injective (Prod.ext (funext fun i ↦
    (Prod.ext_iff.1 (congrFun (Prod.ext_iff.1 h).1 i)).2) (Prod.ext_iff.1 h).2)

/-- **The lockstep round**: copy the query inputs, the calls of every slot before its first
`h`, a round of `h`, the calls between the two `h`, a round of `h`, the remaining calls, and the
removal of the copies. -/
noncomputable def lockRound {A B : QReg} (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E)
    (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B) : QComp (lockSpec X Z) A B Unit :=
  ((isoGate (copyAll dir ℓ) (copyAll_injective dir ℓ)).bind fun _ ↦
    (forSlots (fun j ↦ phaseA π (dir j) j) (List.finRange w)).bind fun _ ↦ roundAll.bind fun _ ↦
      (forSlots (fun j ↦ phaseC π (dir j) j) (List.finRange w)).bind fun _ ↦
        roundAll.bind fun _ ↦ forSlots (fun j ↦ phaseE π (dir j) j) (List.finRange w)).bind
    fun _ ↦ coGate (uncopyAll dir post) (uncopyAll_injective dir post)

end lock

/-! ## The lockstep round against a read runtime -/

section lockSem

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] {w : ℕ} {E D : QReg} (σ₀ : SubState D) (rd : D → SpongeKeys X Z)

/-- A permutation of the register of slot `j`, depending on the runtime state. -/
def slotMap (j : Fin w) (g : D → Equiv.Perm (SlotT X Z)) :
    ((Fin w → SlotT X Z) × E) × D → ((Fin w → SlotT X Z) × E) × D :=
  fun q ↦ ((updEquiv j (g q.2) q.1.1, q.1.2), q.2)

/-- Permutations of the registers of all slots, depending on the runtime state. -/
def allMap (g : Fin w → D → Equiv.Perm (SlotT X Z)) :
    ((Fin w → SlotT X Z) × E) × D → ((Fin w → SlotT X Z) × E) × D :=
  fun q ↦ ((fun i ↦ g i q.2 (q.1.1 i), q.1.2), q.2)

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
theorem slotMap_comp (j : Fin w) (g₁ g₂ : D → Equiv.Perm (SlotT X Z)) :
    slotMap (E := E) j g₂ ∘ slotMap j g₁ = slotMap j fun s ↦ g₂ s * g₁ s := by
  funext q
  refine Prod.ext (Prod.ext (funext fun i ↦ ?_) rfl) rfl
  by_cases h : i = j
  · subst h
    simp [slotMap, updEquiv]
  · simp [slotMap, updEquiv, Function.update_of_ne h]

variable (D) in
/-- The parallel read runtime. -/
noncomputable abbrev readPar : QuantumRuntime (lockSpec X Z) :=
  (readRuntime D σ₀ rd).par spongeHPort

variable {σ₀ rd}

theorem RunsAs.bind_slot {j : Fin w} {x y : QComp (lockSpec X Z) (lockReg X Z w E)
      (lockReg X Z w E) Unit} {g₁ g₂ : D → Equiv.Perm (SlotT X Z)}
    (hx : RunsAs (readPar D σ₀ rd) x (slotMap j g₁))
    (hy : RunsAs (readPar D σ₀ rd) y (slotMap j g₂)) :
    RunsAs (readPar D σ₀ rd) (x.bind fun _ ↦ y) (slotMap j fun s ↦ g₂ s * g₁ s) :=
  (hx.bind hy).congr fun q ↦ congrFun (slotMap_comp j g₁ g₂) q

variable (σ₀ rd)

theorem runsAs_gateAt (j : Fin w) (e : Equiv.Perm (SlotT X Z)) :
    RunsAs (readPar D σ₀ rd) (gateAt (E := E) j e) (slotMap j fun _ ↦ e) :=
  (runsAs_isoGate _ _).congr fun _ ↦ rfl

theorem runsAs_capAt (j : Fin w) (p : SpongePort) (e : (X × Z) ≃ spongeIn X Z p) :
    RunsAs (readPar D σ₀ rd) (capAt (E := E) j p e)
      (slotMap j fun s ↦ stateE (e.trans ((spongeKeyEquiv (rd s) p).trans e.symm))) := by
  unfold capAt
  have : Unique ((lockSpec X Z).Result (.inl p)) := inferInstanceAs (Unique Unit)
  refine (RunsAs.queryBind (R := readPar D σ₀ rd) (i := .inl p)
    (stepMap (readRuntime D σ₀ rd) (fun p s ↦ spongeKeyEquiv (rd s) p) p)
    (fun r ↦ readRuntime_branch p r) _ _ fun _ ↦ runsAs_isoGate _ _).congr fun q ↦ ?_
  refine Prod.ext (Prod.ext (funext fun i ↦ ?_) rfl) rfl
  change ((slotSplit j).symm (e.symm (spongeKeyEquiv (rd q.2) p (e (q.1.1 j).1)),
    (((q.1.1 j).2, fun i ↦ q.1.1 i.1), q.1.2))).1 i =
      updEquiv j (stateE (e.trans ((spongeKeyEquiv (rd q.2) p).trans e.symm))) q.1.1 i
  rw [slotSplit_symm_apply, updEquiv_apply]
  by_cases h : i = j
  · subst h
    simp [stateE]
    rfl
  · simp [h]

theorem runsAs_kAt (j : Fin w) :
    RunsAs (readPar D σ₀ rd) (kAt (E := E) j)
      (slotMap j fun s ↦ stateE (capacityRound (rd s).2.1)) :=
  (runsAs_capAt σ₀ rd j .k (Equiv.refl _)).congr fun _ ↦ rfl

theorem runsAs_k'At (j : Fin w) :
    RunsAs (readPar D σ₀ rd) (k'At (E := E) j)
      (slotMap j fun s ↦ stateE (capacityRound (rd s).2.2)) :=
  (runsAs_capAt σ₀ rd j .k' (Equiv.refl _)).congr fun _ ↦ rfl

variable (X Z) in
/-- `σ_k⁻¹` on a slot, as the call of `k` between two negations of the capacity. -/
def kInvP (k : X → Z) : Equiv.Perm (SlotT X Z) :=
  stateE (negCap X Z) * stateE (capacityRound k) * stateE (negCap X Z)

theorem runsAs_kInvAt (j : Fin w) :
    RunsAs (readPar D σ₀ rd) (kInvAt (E := E) j) (slotMap j fun s ↦ kInvP X Z (rd s).2.1) :=
  RunsAs.bind_slot (runsAs_gateAt σ₀ rd j _)
    (RunsAs.bind_slot (runsAs_kAt σ₀ rd j) (runsAs_gateAt σ₀ rd j _))

theorem runsAs_k'InvAt (j : Fin w) :
    RunsAs (readPar D σ₀ rd) (k'InvAt (E := E) j) (slotMap j fun s ↦ kInvP X Z (rd s).2.2) :=
  RunsAs.bind_slot (runsAs_gateAt σ₀ rd j _)
    (RunsAs.bind_slot (runsAs_k'At σ₀ rd j) (runsAs_gateAt σ₀ rd j _))

variable (π : Equiv.Perm (X × Z))

/-- The permutation of a slot's register before its first `h`. -/
def permA (p : PermutationPort) (t : SpongeKeys X Z) : Equiv.Perm (SlotT X Z) :=
  match p with
  | .forward => stateE (capacityRound t.2.2) * stateE π * stateE (capacityRound t.2.1)
  | .inverse => stateE (negRate X Z)

/-- The permutation of a slot's register between its two `h`. -/
def permC (p : PermutationPort) (t : SpongeKeys X Z) : Equiv.Perm (SlotT X Z) :=
  match p with
  | .forward => stateE (negRate X Z) * addT
  | .inverse => stateE (capacityRound t.2.2) * stateE π * stateE (capacityRound t.2.1) * addT *
      kInvP X Z t.2.1 * stateE π⁻¹ * kInvP X Z t.2.2 * stateE (negRate X Z)

/-- The permutation of a slot's register after its second `h`. -/
def permE (p : PermutationPort) (t : SpongeKeys X Z) : Equiv.Perm (SlotT X Z) :=
  match p with
  | .forward => kInvP X Z t.2.1 * stateE π⁻¹ * kInvP X Z t.2.2 * stateE (negRate X Z)
  | .inverse => 1

theorem runsAs_phaseA (p : PermutationPort) (j : Fin w) :
    RunsAs (readPar D σ₀ rd) (phaseA (E := E) π p j) (slotMap j fun s ↦ permA π p (rd s)) := by
  cases p
  · exact RunsAs.bind_slot (runsAs_kAt σ₀ rd j)
      (RunsAs.bind_slot (runsAs_gateAt σ₀ rd j _) (runsAs_k'At σ₀ rd j))
  · exact runsAs_gateAt σ₀ rd j _

theorem runsAs_phaseC (p : PermutationPort) (j : Fin w) :
    RunsAs (readPar D σ₀ rd) (phaseC (E := E) π p j) (slotMap j fun s ↦ permC π p (rd s)) := by
  cases p
  · exact RunsAs.bind_slot (runsAs_gateAt σ₀ rd j _) (runsAs_gateAt σ₀ rd j _)
  · exact RunsAs.bind_slot (runsAs_gateAt σ₀ rd j _) (RunsAs.bind_slot (runsAs_k'InvAt σ₀ rd j)
      (RunsAs.bind_slot (runsAs_gateAt σ₀ rd j _) (RunsAs.bind_slot (runsAs_kInvAt σ₀ rd j)
        (RunsAs.bind_slot (runsAs_gateAt σ₀ rd j _) (RunsAs.bind_slot (runsAs_kAt σ₀ rd j)
          (RunsAs.bind_slot (runsAs_gateAt σ₀ rd j _) (runsAs_k'At σ₀ rd j)))))))

theorem runsAs_phaseE (p : PermutationPort) (j : Fin w) :
    RunsAs (readPar D σ₀ rd) (phaseE (E := E) π p j) (slotMap j fun s ↦ permE π p (rd s)) := by
  cases p
  · exact RunsAs.bind_slot (runsAs_gateAt σ₀ rd j _) (RunsAs.bind_slot (runsAs_k'InvAt σ₀ rd j)
      (RunsAs.bind_slot (runsAs_gateAt σ₀ rd j _) (runsAs_kInvAt σ₀ rd j)))
  · refine runsAs_pure.congr fun q ↦ ?_
    refine Prod.ext (Prod.ext (funext fun i ↦ ?_) rfl) rfl
    simp [slotMap, permE, updEquiv_apply]

theorem runsAs_forSlots
    {P : Fin w → QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit}
    {g : Fin w → D → Equiv.Perm (SlotT X Z)}
    (hP : ∀ j, RunsAs (readPar D σ₀ rd) (P j) (slotMap j (g j))) :
    ∀ l : List (Fin w), l.Nodup → RunsAs (readPar D σ₀ rd) (forSlots P l)
      (fun q ↦ ((fun i ↦ if i ∈ l then g i q.2 (q.1.1 i) else q.1.1 i, q.1.2), q.2))
  | [], _ => runsAs_pure.congr fun q ↦ by simp
  | j :: l, hl => by
    rw [List.nodup_cons] at hl
    refine ((hP j).bind (runsAs_forSlots hP l hl.2)).congr fun q ↦ ?_
    refine Prod.ext (Prod.ext (funext fun i ↦ ?_) rfl) rfl
    by_cases h : i = j
    · subst h
      simp [slotMap, updEquiv_apply, hl.1]
    · simp [slotMap, updEquiv_apply, h]

theorem runsAs_forSlots_all
    {P : Fin w → QComp (lockSpec X Z) (lockReg X Z w E) (lockReg X Z w E) Unit}
    {g : Fin w → D → Equiv.Perm (SlotT X Z)}
    (hP : ∀ j, RunsAs (readPar D σ₀ rd) (P j) (slotMap j (g j))) :
    RunsAs (readPar D σ₀ rd) (forSlots P (List.finRange w)) (allMap g) :=
  (runsAs_forSlots σ₀ rd hP _ (List.nodup_finRange w)).congr fun q ↦ by simp [allMap]

theorem runsAs_roundAll :
    RunsAs (readPar D σ₀ rd) (roundAll (X := X) (Z := Z) (w := w) (E := E))
      (allMap fun _ s ↦ stateE (rateRound (rd s).1)) := by
  unfold roundAll
  have : Unique ((lockSpec X Z).Result (.inr (.round w fun _ ↦ ()))) :=
    inferInstanceAs (Unique (Fin w → Unit))
  exact (RunsAs.queryBind (R := readPar D σ₀ rd) (i := .inr (.round w fun _ ↦ ())) _
    (fun r ↦ branch_roundStep_basis (R := readRuntime D σ₀ rd)
      (G := fun p s ↦ spongeKeyEquiv (rd s) p) (fun p r ↦ readRuntime_branch p r) _ r) _ _
    fun _ ↦ runsAs_isoGate _ _).congr fun _ ↦ rfl

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
theorem stateE_apply (e : Equiv.Perm (X × Z)) (u : SlotT X Z) : stateE e u = (e u.1, u.2) :=
  rfl

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem addT_apply (u : SlotT X Z) : addT u = (u.1, (u.2.1, u.2.2 + u.1)) :=
  rfl

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] in
theorem kInvP_apply (k : X → Z) (u : SlotT X Z) :
    kInvP X Z k u = ((capacityRound k)⁻¹ u.1, u.2) := by
  simp [kInvP, stateE_apply, negCap, capacityRound_inv_apply, sub_eq_add_neg, add_comm]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
theorem negRate_rateRound_negRate (h : Z → X) (u : SlotT X Z) :
    stateE (negRate X Z) (stateE (rateRound h) (stateE (negRate X Z) u)) =
      ((rateRound h)⁻¹ u.1, u.2) := by
  simp [stateE_apply, negRate, rateRound_inv_apply, sub_eq_add_neg, add_comm]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- **One slot in lockstep**: from the copied input, the permutations of the slot make the call
of the port. -/
theorem slot_lockstep (p : PermutationPort) (t : SpongeKeys X Z) (v : (X × Z) × (X × Z)) :
    permE π p t (stateE (rateRound t.1) (permC π p t (stateE (rateRound t.1)
      (permA π p t (v.1, v))))) = (v.1, oracleEquiv (portPerm (spongePerm t π) p) v) := by
  cases p
  · simp only [permA, permC, permE, Equiv.Perm.mul_apply]
    rw [negRate_rateRound_negRate]
    simp only [kInvP_apply, stateE_apply, addT_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rfl
  · simp only [permA, permC, permE, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    rw [negRate_rateRound_negRate]
    simp only [kInvP_apply, stateE_apply, addT_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    rfl

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
theorem allMap_comp (g₁ g₂ : Fin w → D → Equiv.Perm (SlotT X Z)) :
    allMap (E := E) g₂ ∘ allMap g₁ = allMap fun i s ↦ g₂ i s * g₁ i s :=
  rfl

variable (dir : Fin w → PermutationPort)

/-- **The lockstep round runs as the round of the permutation oracle read off the register.** -/
theorem runsAs_lockRound {A B : QReg} (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E)
    (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B) :
    RunsAs (readPar D σ₀ rd) (lockRound π dir ℓ post) (fun q : A × D ↦
      (post ((fun i ↦ oracleEquiv (portPerm (spongePerm (rd q.2) π) (dir i)) ((ℓ q.1).1 i) :
        ∀ i, (qrpmSpec (X × Z)).Out (dir i)), (ℓ q.1).2), q.2)) := by
  unfold lockRound
  refine RunsAs.bind_coGate ((runsAs_isoGate _ _).bind
    ((runsAs_forSlots_all σ₀ rd fun j ↦ runsAs_phaseA σ₀ rd π (dir j) j).bind
      ((runsAs_roundAll σ₀ rd).bind
        ((runsAs_forSlots_all σ₀ rd fun j ↦ runsAs_phaseC σ₀ rd π (dir j) j).bind
          ((runsAs_roundAll σ₀ rd).bind
            (runsAs_forSlots_all σ₀ rd fun j ↦ runsAs_phaseE σ₀ rd π (dir j) j))))))
    _ _ _ fun q ↦ ?_
  refine Prod.ext (Prod.ext (funext fun i ↦ ?_) ?_) rfl
  · simp only [Function.comp_apply, Prod.map, allMap, copyAll, uncopyAll, id,
      Equiv.symm_apply_apply]
    exact slot_lockstep π (dir i) (rd q.2) ((ℓ q.1).1 i)
  · simp [Function.comp_apply, Prod.map, allMap, copyAll, uncopyAll]

/-- **Lockstep = serialized simulation, against a read runtime.** -/
theorem branch_run₂_simulate_seqCalls_read {A B : QReg}
    (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E) (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B)
    (rs : RoundResult (qrpmSpec (X × Z)) dir) :
    ((readRuntime D σ₀ rd).run₂ .instruments
        (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post))).branch rs =
      ((readPar D σ₀ rd).run₂ .instruments (lockRound π dir ℓ post)).branch () := by
  have h1 : (readRuntime D σ₀ rd).run₂ .instruments
      (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post)) =
        (permReadRuntime D σ₀ π rd).run₂ .instruments (seqCalls dir E ℓ post) :=
    congrArg (fun P ↦ DSubInstrument.comap (QuantumComp₂.leafEquiv B
      (RoundResult (qrpmSpec (X × Z)) dir)) (QuantumComp₂.leafEquiv B _).injective P)
      (run_simulate_read σ₀ rd (L := LocalSig.instruments.{0})
        (W := QuantumComp₂.Leaf B (RoundResult (qrpmSpec (X × Z)) dir))
        LocalSig.Interp.instruments π (seqCalls dir E ℓ post))
  rw [h1, branch_run₂_seqCalls_basis (fun p r ↦ permReadRuntime_branch σ₀ rd π p r)]
  exact (runsAs_lockRound σ₀ rd π dir ℓ post).symm

end lockSem

/-! ## Runtimes that read their functions in a unitary basis -/

section transfer

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] (R : QuantumRuntime (spongeSpec X Z)) (U : Matrix R.D R.D ℂ)
  (hU : U ∈ unitaryGroup R.D ℂ) (rd : R.D → SpongeKeys X Z) (hR : IsReadRuntime R U rd)

include hU hR in
/-- A read runtime in the basis of `U` runs every program as the read runtime, conjugated. -/
theorem branch_run₂_eq_conj_read {A B : QReg} {α : Type}
    (x : QuantumComp₂ LocalSig.instruments.{0} (spongeSpec X Z) A B α) (a : α) :
    (R.run₂ .instruments x).branch a =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ Uᴴ) ∘ₗ
        ((readRuntime R.D R.init rd).run₂ .instruments x).branch a ∘ₗ
          MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ U) := by
  have hUU : U * Uᴴ = 1 := by
    rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hU
  have hUU' : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have hsim : ∀ i r, (R.step i).branch r ∘ₗ (MatrixMap.conj Uᴴ).amplifyLeft
      ((spongeSpec X Z).In i) = (MatrixMap.conj Uᴴ).amplifyLeft ((spongeSpec X Z).Out i) ∘ₗ
        ((readRuntime R.D R.init rd).step i).branch r := fun i r ↦ by
    rw [show r = () from rfl, hR i, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul]
    refine (congrArg MatrixMap.conj ?_).trans ((MatrixMap.conj_mul _ _).trans
      (congrArg (MatrixMap.conj _ ∘ₗ ·) (branch_relabel (readEquiv rd i) ()).symm))
    rw [Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.one_mul, hUU, one_kronecker_one,
      Matrix.mul_one]
  have h := QuantumRuntime.simulation₂ .instruments (R₁ := readRuntime R.D R.init rd) (R₂ := R)
    (V := MatrixMap.conj Uᴴ) hsim x a
  rw [MatrixMap.amplifyLeft_conj, MatrixMap.amplifyLeft_conj] at h
  refine LinearMap.ext fun ρ ↦ ?_
  have hρ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Uᴴ)
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ U) ρ) = ρ := by
    rw [← LinearMap.comp_apply, ← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul, hUU',
      one_kronecker_one, MatrixMap.conj_one, LinearMap.id_apply]
  have h' : (R.run₂ .instruments x).branch a (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Uᴴ)
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ U) ρ)) =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ Uᴴ) (((readRuntime R.D R.init rd).run₂ .instruments
        x).branch a (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ U) ρ)) :=
    LinearMap.congr_fun h _
  rw [hρ] at h'
  exact h'

include hU hR in
/-- **Lockstep = serialized simulation**, against every runtime that reads its functions in the
basis of a unitary: the serialized simulation of a round of permutation calls and the lockstep
round have the same run. -/
theorem branch_run₂_simulate_seqCalls_eq_lockRound (π : Equiv.Perm (X × Z)) {w : ℕ}
    (dir : Fin w → PermutationPort) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E) (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B)
    (rs : RoundResult (qrpmSpec (X × Z)) dir) :
    (R.run₂ .instruments (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post))).branch
        rs = ((R.par spongeHPort).run₂ .instruments (lockRound π dir ℓ post)).branch () := by
  have hpar : (R.par spongeHPort).run₂ .instruments (lockRound π dir ℓ post) =
      R.run₂ .instruments (IFreeM.substitute (parToSeq (spec := spongeSpec X Z) spongeHPort)
        (lockRound π dir ℓ post)) :=
    congrArg (fun P ↦ DSubInstrument.comap (QuantumComp₂.leafEquiv B Unit)
      (QuantumComp₂.leafEquiv B Unit).injective P)
      (R.run_substitute_parToSeq spongeHPort (lockRound π dir ℓ post)).symm
  have hpar' : (readPar R.D R.init rd).run₂ .instruments (lockRound π dir ℓ post) =
      (readRuntime R.D R.init rd).run₂ .instruments
        (IFreeM.substitute (parToSeq (spec := spongeSpec X Z) spongeHPort)
          (lockRound π dir ℓ post)) :=
    congrArg (fun P ↦ DSubInstrument.comap (QuantumComp₂.leafEquiv B Unit)
      (QuantumComp₂.leafEquiv B Unit).injective P)
      ((readRuntime R.D R.init rd).run_substitute_parToSeq spongeHPort
        (lockRound π dir ℓ post)).symm
  have e1 := branch_run₂_eq_conj_read R U hU rd hR
    (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post)) rs
  have e2 := branch_run₂_eq_conj_read R U hU rd hR
    (IFreeM.substitute (parToSeq (spec := spongeSpec X Z) spongeHPort)
      (lockRound π dir ℓ post)) ()
  have e3 := branch_run₂_simulate_seqCalls_read R.init rd π dir ℓ post rs
  refine e1.trans (Eq.trans ?_ (e2.symm.trans (congrArg (fun P ↦ P.branch ()) hpar.symm)))
  exact congrArg (fun L ↦ MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ Uᴴ) ∘ₗ L ∘ₗ
    MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ U)) (e3.trans (congrArg (fun P ↦ P.branch ()) hpar'))

end transfer

end Quantum.Par

end
