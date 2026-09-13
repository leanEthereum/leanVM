import XmssSecurity.Proof.Deterministic.SignerSampling
import XmssSecurity.Proof.Deterministic.TranscriptReduction

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev RequestTapes := SignRequest → TrialTape

noncomputable opaque requestTapesSampleableType : SampleableType RequestTapes := SampleableType.ofFintype RequestTapes
noncomputable local instance : SampleableType RequestTapes := requestTapesSampleableType
noncomputable local instance : SampleableType TrialTape := trialTapeSampleableType
noncomputable local instance : SampleableType RandomizerOutputs := randomizerOutputsSampleableType

noncomputable def sampleRequestTapes : ProbComp RequestTapes := $ᵗ RequestTapes

theorem evalDist_curry_randomizers :
    𝒟[Equiv.curry SignRequest Trial HashOutput <$> sampleRandomizerOutputs] = 𝒟[sampleRequestTapes] :=
  evalDist_map_bijective_uniform_cross (α := RandomizerOutputs) (β := RequestTapes) _ (Equiv.curry SignRequest Trial HashOutput).bijective

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]

omit [LawfulMonad m] in
theorem tableSignFrom_own (randomizers : RandomizerOutputs) (secretKey : XmssSecurity.SecretKey)
    (message : SignRequest) (attempts trial : Nat) :
    (tableSignFrom randomizers secretKey message.epoch message.message attempts trial : m TrialResult) =
      tableSignFrom (fun position => randomizers (message, position.2)) secretKey message.epoch message.message attempts trial := by
  induction attempts generalizing trial with
  | zero => rfl
  | succ attempts ih =>
      simp only [tableSignFrom]
      apply bind_congr
      intro result
      cases result with
      | none => exact ih _
      | some result => rfl

omit [LawfulMonad m] in
theorem tableSign_own (randomizers : RandomizerOutputs) (secretKey : XmssSecurity.SecretKey) (message : SignRequest) :
    (tableSign randomizers secretKey message.epoch message.message : m (Option Signature)) =
      tableSign (fun position => randomizers (message, position.2)) secretKey message.epoch message.message := by
  unfold tableSign
  rw [tableSignFrom_own randomizers secretKey message]

attribute [local irreducible] tableSign

variable {State : Type}

noncomputable def requestKernel (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : XmssSecurity.SecretKey) (message : SignRequest) (tape : TrialTape) :
    StateT State ProbComp (Option Signature) :=
  simulateQ (worldHandler hash) (liftM (tableSign (fun position => tape position.2) secretKey message.epoch message.message :
    OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature))

theorem simulateQ_runSigning {α : Type} (handler : QueryImpl OracleWorld (StateT State ProbComp))
    (sign : SignRequest → OracleComp HashSpec (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ handler (runSigning sign computation) =
      simulateQ (handler + fun (message : SignRequest) => simulateQ handler (liftM (sign message) : OracleComp OracleWorld _)) computation := by
  rw [runSigning, ← QueryImpl.simulateQ_compose]
  apply congrArg (fun implementation => simulateQ implementation computation)
  funext input
  cases input with
  | inl input =>
      change simulateQ handler (liftM (OracleWorld.query input) : OracleComp OracleWorld _) = handler input
      exact simulateQ_spec_query handler input
  | inr input => rfl

theorem tableRun_lift_requests {α Tape : Type}
    (handler : QueryImpl OracleWorld (StateT State ProbComp))
    (kernel : SignRequest → Tape → OracleComp HashSpec (Option Signature))
    (sign : SignRequest → OracleComp HashSpec (Option Signature))
    (tapes : SignRequest → Tape)
    (hsign : ∀ message, kernel message (tapes message) = sign message)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    tableRun handler (fun (message : SignRequest) tape => simulateQ handler
      (liftM (kernel message tape) : OracleComp OracleWorld (Option Signature))) tapes computation =
      simulateQ handler (runSigning sign computation) := by
  rw [simulateQ_runSigning]
  unfold tableRun
  apply congrArg (fun implementation => simulateQ implementation computation)
  funext input
  cases input with
  | inl input => rfl
  | inr message =>
      exact congrArg (fun signing : OracleComp HashSpec (Option Signature) =>
        simulateQ handler (liftM signing : OracleComp OracleWorld (Option Signature))) (hsign message)

theorem tableRun_requests {α : Type} (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : XmssSecurity.SecretKey) (tapes : RequestTapes)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    tableRun (worldHandler hash) (requestKernel hash secretKey) tapes computation =
      simulateQ (worldHandler hash) (runSigning (fun (message : SignRequest) => tableSign (Function.uncurry tapes) secretKey message.epoch message.message) computation) := by
  exact tableRun_lift_requests (worldHandler hash)
    (fun (message : SignRequest) tape => tableSign (fun position => tape position.2) secretKey message.epoch message.message)
    (fun (message : SignRequest) => tableSign (Function.uncurry tapes) secretKey message.epoch message.message) tapes
    (fun (message : SignRequest) => (tableSign_own (m := OracleComp HashSpec) (Function.uncurry tapes) secretKey message).symm)
    computation

theorem evalDist_freshRun_of_kernel {α Tape : Type} [SampleableType Tape]
    (handler : QueryImpl OracleWorld (StateT State ProbComp))
    (kernel : SignRequest → Tape → StateT State ProbComp (Option Signature))
    (sign : SignRequest → StateT State ProbComp (Option Signature))
    (hkernel : ∀ message state, 𝒟[do
      let tape ← ($ᵗ Tape : ProbComp Tape)
      (kernel message tape).run state] = 𝒟[(sign message).run state])
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : State) :
    𝒟[(freshRun handler kernel computation).run state] =
      𝒟[(simulateQ (handler + sign) computation).run state] := by
  unfold freshRun
  apply evalDist_simulateQ_run_congr
  intro input state
  cases input with
  | inl input => rfl
  | inr message =>
      change 𝒟[((do
        let tape ← liftM ($ᵗ Tape : ProbComp Tape)
        kernel message tape) : StateT State ProbComp (Option Signature)).run state] = _
      simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]
      exact hkernel message state

theorem evalDist_freshRequests {α : Type} (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : XmssSecurity.SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α) (state : State) :
    𝒟[(freshRun (worldHandler hash) (requestKernel hash secretKey) computation).run state] =
      𝒟[(simulateQ ((worldHandler hash) + fun (message : SignRequest) => simulateQ (worldHandler hash)
        (Concrete.precomputedCappedSign secretKey message.epoch message.message)) computation).run state] := by
  exact evalDist_freshRun_of_kernel (worldHandler hash) (requestKernel hash secretKey)
    (fun (message : SignRequest) => simulateQ (worldHandler hash)
      (Concrete.precomputedCappedSign secretKey message.epoch message.message))
    (fun message state => evalDist_tableSign hash secretKey message.epoch message.message state)
    computation state

theorem evalDist_uncurry_tapes :
    𝒟[Function.uncurry <$> sampleRequestTapes] = 𝒟[sampleRandomizerOutputs] :=
  evalDist_map_bijective_uniform_cross (α := RequestTapes) (β := RandomizerOutputs) _ (Equiv.curry SignRequest Trial HashOutput).symm.bijective

theorem evalDist_tableRequests {α : Type} {used : Set SignRequest}
    (hash : QueryImpl HashSpec (StateT State ProbComp)) (secretKey : XmssSecurity.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (hfresh : FreshRequests used computation) (state : State) :
    𝒟[do
      let randomizers ← sampleRandomizerOutputs
      (simulateQ (worldHandler hash) (runSigning (fun (message : SignRequest) => tableSign randomizers secretKey message.epoch message.message) computation)).run state] =
      𝒟[(simulateQ ((worldHandler hash) + fun (message : SignRequest) => simulateQ (worldHandler hash)
        (Concrete.precomputedCappedSign secretKey message.epoch message.message)) computation).run state] := by
  conv_lhs => rw [evalDist_bind, ← evalDist_uncurry_tapes, ← evalDist_bind, bind_map_left]
  simp_rw [← tableRun_requests]
  exact (hfresh.evalDist_tableRun (worldHandler hash) (requestKernel hash secretKey) state).trans
    (evalDist_freshRequests hash secretKey computation state)

theorem freshRequests_sourceGame_memo (publicKey : PublicKey) (adversary : Adversary) :
    FreshRequests ∅ (sourceGame publicKey (memoAdversary adversary)) := by
  have h : FreshRequests ∅ (memoize (adversary.main publicKey) ∅) := by
    simpa only [QueryCache.empty_apply, ne_eq, not_true_eq_false, Set.setOf_false] using
      freshRequests_memoize (adversary.main publicKey) ∅
  unfold sourceGame memoAdversary
  apply h.withRequestLog.bind
  intro result used
  rw [← bind_pure (baseLift (finishGame publicKey result))]
  exact freshRequests_base_bind used (finishGame publicKey result) _ (fun value => .pure value)

end XmssSecurity.Seeded
