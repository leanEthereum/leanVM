import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualComposition
import SphincsSecurity.Proof.Residual.RetainedSigningTrace
import SphincsSecurity.Proof.Fts.StoppedSigningLog
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open FtsProbeSimulation (withSigningLog)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  signDigestLoop signAfterDigest sequenceFin chainWalk
set_option backward.isDefEq.respectTransparency false

def StoppedOr {Result : Type} (event : Result → QueryLog SigningSpec → Prop) (result : Option Result × Memory) : Prop :=
  result.1.elim True (fun value => event value result.2.log)

theorem fixedHashStep_answer {inputs : Finset HashInput} (context : Context inputs) (input : HashInput) (memory : Memory) :
    (fixedHashStep context.key.parameter context.words context.auxiliary.selections memory.routing context.actual context.oracle input memory).1 = none ∨
    (fixedHashStep context.key.parameter context.words context.auxiliary.selections memory.routing context.actual context.oracle input memory).1 =
      some (context.oracle input) := by
  unfold fixedHashStep ResidualByteFrontend.fixedStep ResidualByteFrontend.fixedAnswer ResidualByteFrontend.checkedResult
  split
  · exact Or.inl rfl
  · dsimp only [Option.bind_some]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem fixedHashStep_log {inputs : Finset HashInput} (context : Context inputs) (input : HashInput) (memory : Memory) :
    (fixedHashStep context.key.parameter context.words context.auxiliary.selections memory.routing context.actual context.oracle input memory).2.log =
      memory.log := by
  exact congrArg (fun history => history.2.1) (afterReply_history context.key.parameter memory input _ _)

private theorem fixedOriginal_sign_bind {Result : Type} (key : SecretKey) (oracle : QueryImpl HashSpec Id)
    (message : Message) (next : Option Signature → OracleComp OracleWorld Result) :
    simulateQ (fixedHashWorld oracle) (scheme.sign key message >>= next) =
      fixedBoundaryRun key.parameter oracle (signWithView key message) >>= fun record =>
        simulateQ (fixedHashWorld oracle) (next record.1.1) := by
  rw [show scheme.sign key message = sign key message from rfl,
    ← signWithView_fst key message, bind_map_left, simulateQ_bind,
    ← fixedBoundaryRun_forget key.parameter oracle (signWithView key message), bind_map_left]

theorem prob_originalSource_le_stopped {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (memory : Memory)
    (event : Result → QueryLog SigningSpec → Prop) :
    Pr[fun result => event result.1 result.2 |
      simulateQ (fixedHashWorld context.oracle)
        (simulateQ (expandedAdversaryImpl context.key) (withSigningLog computation memory.log))] ≤
      Pr[StoppedOr event | fixedSourceRun context computation memory] := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure value =>
      simp only [FtsProbeSimulation.withSigningLog_pure, simulateQ_pure, fixedSourceRun_pure,
        probEvent_pure, StoppedOr, Option.elim_some, le_refl]
  | query_bind input next ih =>
      rw [FtsProbeSimulation.withSigningLog_query_bind, fixedSourceRun_query_bind]
      cases input with
      | inl input =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inl, simulateQ_bind, simulateQ_spec_query]
          simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, fixedByteRun, simulateQ_spec_query,
            signingLogFragment, List.append_nil]
          cases input with
          | inl input =>
              simp only [fixedHashWorld, fixedByteImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind,
                Option.elim_some, probEvent_bind_eq_tsum, probOutput_query, SPMF.probOutput_liftM,
                PMF.probOutput_eq_apply, PMF.uniformOfFintype_apply]
              apply ENNReal.tsum_le_tsum
              intro answer
              exact mul_le_mul' le_rfl (ih answer memory)
          | inr input =>
              simp only [fixedHashWorld, fixedByteImpl, OptionT.run_mk, StateT.run_mk, pure_bind]
              rcases fixedHashStep_answer context input memory with hstop | hlive
              · rw [hstop, Option.elim_none]
                simp only [probEvent_pure, StoppedOr, Option.elim_none, if_true]
                exact probEvent_le_one
              · rw [hlive, Option.elim_some]
                have h := ih (context.oracle input)
                  (fixedHashStep context.key.parameter context.words context.auxiliary.selections memory.routing context.actual context.oracle input memory).2
                rw [fixedHashStep_log] at h
                exact h
      | inr message =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inr, fixedOriginal_sign_bind]
          simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, bind_map_left, Option.elim_some,
            probEvent_bind_eq_tsum]
          apply ENNReal.tsum_le_tsum
          intro record
          apply mul_le_mul'
          · simp only [probOutput_def, SPMF.evalDist_def, le_refl]
          · have h := ih record.1.1 ((memory.applyBoundary record.2).recordSigning message record)
            have hlog : ((memory.applyBoundary record.2).recordSigning message record).log =
                memory.log ++ signingLogFragment (.inr message) record.1.1 := rfl
            rw [hlog] at h
            exact h

def sourceVerdict (result : Forgery × Bool) (log : QueryLog SigningSpec) : Bool :=
  decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log result.1) && result.2

theorem fixedOriginal_gameRest (key : SecretKey) (oracle : QueryImpl HashSpec Id) (adversary : Adversary) :
    simulateQ (fixedHashWorld oracle) (gameRest scheme adversary ⟨key.root, key.parameter⟩ key) =
      (fun result => sourceVerdict result.1 result.2) <$>
        simulateQ (fixedHashWorld oracle) (simulateQ (expandedAdversaryImpl key)
          (withSigningLog (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) [])) := by
  rw [← FtsProbeSimulation.simulateQ_expanded_tracedGameRestComputation,
    ← FtsProbeSimulation.retainedGameRestComputation_verdict_projection,
    FtsProbeSimulation.retainedGameRestComputation_eq_signingTrace]
  simp only [simulateQ_map, Functor.map_map, withSigningLog, List.nil_append]
  rfl

theorem prob_gameRest_le_stopped {inputs : Finset HashInput} (context : Context inputs)
    (adversary : Adversary) (memory : Memory) (hlog : memory.log = []) :
    Pr[fun verdict => verdict = true |
      simulateQ (fixedHashWorld context.oracle)
        (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key)] ≤
      Pr[StoppedOr (fun result log => sourceVerdict result log = true) |
        fixedSourceRun context
          (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩) memory] := by
  rw [fixedOriginal_gameRest, probEvent_map]
  have h := prob_originalSource_le_stopped context
    (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩)
    memory (fun result log => sourceVerdict result log = true)
  rw [hlog] at h
  exact h

theorem prob_gameRest_le_observed {inputs : Finset HashInput} (context : Context inputs)
    (adversary : Adversary)
    (hinputs : sourceInputs context.key
      (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩) ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) (hlog : state.memory.log = []) :
    Pr[fun verdict => verdict = true |
      simulateQ (fixedHashWorld context.oracle)
        (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key)] ≤
      Pr[fun result => StoppedOr (fun value log => sourceVerdict value log = true) (forgetState result) |
        observedRun context.environment context.actual context.auxiliary.seed
          (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections)
            (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩)) state] := by
  have h := prob_gameRest_le_stopped context adversary state.memory hlog
  rw [← observedRun_source_memory context _ hinputs state hcovered hcompatible, probEvent_map] at h
  exact h

end SphincsSecurity.Concrete.RetainedResidual
