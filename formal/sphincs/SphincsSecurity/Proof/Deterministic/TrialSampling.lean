import SphincsSecurity.Proof.Deterministic.TrialLoop
import SphincsSecurity.Proof.Scheme.StatementLemmas

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000

attribute [local irreducible] Concrete.signAttempt

variable {State : Type}

noncomputable def worldHandler (hash : QueryImpl HashSpec (StateT State ProbComp)) :
    QueryImpl OracleWorld (StateT State ProbComp) :=
  ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT State ProbComp)) + hash

theorem worldHandler_lift_prob {α : Type} (hash : QueryImpl HashSpec (StateT State ProbComp))
    (computation : ProbComp α) :
    simulateQ (worldHandler hash) (liftM computation : OracleComp OracleWorld α) =
      (liftM computation : StateT State ProbComp α) := by
  rw [worldHandler, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, simulateQ_ofLift_eq_self]

theorem worldHandler_sampling_bind {α β : Type} (hash : QueryImpl HashSpec (StateT State ProbComp))
    (sampler : ProbComp α) (next : α → OracleComp OracleWorld β) (state : State) :
    (simulateQ (worldHandler hash) ((liftM sampler : OracleComp OracleWorld α) >>= next)).run state =
      (sampler >>= fun value => (simulateQ (worldHandler hash) (next value)).run state) := by
  rw [simulateQ_bind, worldHandler_lift_prob]
  simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]

def trialKernel (_ : Trial) (output : HashOutput) : StateT State ProbComp HashOutput := pure output

theorem trialTableRun_eq (handler : QueryImpl OracleWorld (StateT State ProbComp)) (tape : TrialTape)
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts trial : Nat) :
    tableRun handler trialKernel tape (trialLoop secretKey message attempts trial) =
      simulateQ handler (liftM (tableDigestLoop (fun position => tape position.2) secretKey message attempts trial :
        OracleComp HashSpec TrialResult) : OracleComp OracleWorld TrialResult) := by
  induction attempts generalizing trial with
  | zero => rfl
  | succ attempts ih =>
      simp only [trialLoop, tableDigestLoop, tableRun, simulateQ_bind, simulateQ_spec_query,
        liftM_bind]
      change (pure (tape (BitVec.ofNat 32 trial)) >>= fun output =>
        simulateQ (handler + fun input => trialKernel input (tape input))
          (baseLift (liftM (Concrete.signAttempt secretKey message (truncateHash output) : OracleComp HashSpec _) :
            OracleComp OracleWorld _) : OracleComp TrialWorld _) >>= _) = _
      rw [pure_bind, simulateQ_baseLift]
      apply congrArg (fun k => simulateQ handler
        (liftM (Concrete.signAttempt secretKey message (truncateHash (tape (BitVec.ofNat 32 trial)))) :
          OracleComp OracleWorld _) >>= k)
      funext attempt
      cases attempt with
      | none => exact ih _
      | some result => rfl

theorem evalDist_randomizer :
    𝒟[truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)] = 𝒟[Concrete.sampleRandomness] := by
  apply Eq.trans evalDist_truncateHash_uniform
  simp only [Concrete.sampleRandomness_eq, evalDist_uniformSample]

theorem run_freshTrialLoop_succ (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts trial : Nat) (state : State) :
    (freshRun (worldHandler hash) trialKernel (trialLoop secretKey message (attempts + 1) trial)).run state = (do
      let output ← ($ᵗ HashOutput : ProbComp HashOutput)
      let result ← (simulateQ (worldHandler hash) (liftM
        (Concrete.signAttempt secretKey message (truncateHash output) : OracleComp HashSpec _) : OracleComp OracleWorld _)).run state
      (freshRun (worldHandler hash) trialKernel (match result.1 with
        | none => trialLoop secretKey message attempts (trial + 1)
        | some (index, leaves) => pure (some (truncateHash output, index, leaves)))).run result.2) := by
  rw [trialLoop, freshRun_request_bind]
  simp only [trialKernel, pure_bind]
  simp_rw [freshRun_baseLift_bind]
  simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]
  apply bind_congr
  intro output
  apply bind_congr
  intro result
  cases result.1 <;> rfl

theorem run_randomTrialLoop_succ (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts : Nat) (state : State) :
    (simulateQ (worldHandler hash) (Concrete.signDigestLoop (attempts + 1) secretKey message)).run state = (do
      let randomness ← Concrete.sampleRandomness
      let result ← (simulateQ (worldHandler hash) (liftM
        (Concrete.signAttempt secretKey message randomness : OracleComp HashSpec _) : OracleComp OracleWorld _)).run state
      (simulateQ (worldHandler hash) (match result.1 with
        | none => Concrete.signDigestLoop attempts secretKey message
        | some (index, leaves) => pure (some (randomness, index, leaves)))).run result.2) := by
  rw [Concrete.signDigestLoop, worldHandler_sampling_bind]
  apply bind_congr
  intro randomness
  simp only [simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro result
  cases result.1 <;> rfl

theorem evalDist_freshTrialLoop (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts trial : Nat) (state : State) :
    𝒟[(freshRun (worldHandler hash) trialKernel (trialLoop secretKey message attempts trial)).run state] =
      𝒟[(simulateQ (worldHandler hash) (Concrete.signDigestLoop attempts secretKey message)).run state] := by
  induction attempts generalizing trial state with
  | zero => rfl
  | succ attempts ih =>
      rw [run_freshTrialLoop_succ, run_randomTrialLoop_succ]
      conv_rhs => rw [evalDist_bind, ← evalDist_randomizer, ← evalDist_bind, bind_map_left]
      apply evalDist_bind_congr'
      intro output
      apply evalDist_bind_congr'
      intro result
      cases result.1 with
      | none => exact ih (trial + 1) result.2
      | some indices => rfl

noncomputable local instance : SampleableType TrialTape := trialTapeSampleableType

theorem evalDist_tableDigestLoop (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts trial : Nat)
    (hbound : trial + attempts ≤ 2 ^ 32) (state : State) :
    𝒟[do
      let tape ← sampleTrialTape
      (simulateQ (worldHandler hash) (liftM (tableDigestLoop (fun position => tape position.2)
        secretKey message attempts trial : OracleComp HashSpec TrialResult) : OracleComp OracleWorld TrialResult)).run state] =
      𝒟[(simulateQ (worldHandler hash) (Concrete.signDigestLoop attempts secretKey message)).run state] := by
  simp_rw [← trialTableRun_eq]
  exact ((freshRequests_trialLoop secretKey message attempts trial hbound).evalDist_tableRun
    (worldHandler hash) trialKernel state).trans
      (evalDist_freshTrialLoop hash secretKey message attempts trial state)

end SphincsSecurity.Seeded
