import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualProposalStep
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

noncomputable def proposalImpl : QueryImpl (OracleWorld + SigningSpec) (OptionT (StateT (ProposalState inputs) SPMF)) :=
  fun input => OptionT.mk (StateT.mk (proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input))

noncomputable def proposalRun {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ProposalState inputs) : SPMF (Option Result × ProposalState inputs) :=
  (simulateQ (proposalImpl key inputs hencoding words publicReplies selections rows budget required stopAfter) computation).run.run state

theorem proposalRun_pure {Result : Type} (value : Result) (state : ProposalState inputs) :
    proposalRun key inputs hencoding words publicReplies selections rows budget required stopAfter (pure value) state =
      pure (some value, state) := by
  simp only [proposalRun, simulateQ_pure, OptionT.run_pure, StateT.run_pure]

theorem proposalRun_query_bind {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result)
    (state : ProposalState inputs) :
    proposalRun key inputs hencoding words publicReplies selections rows budget required stopAfter
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
      (proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state >>= fun result =>
        result.1.elim (pure (none, result.2)) fun answer =>
          proposalRun key inputs hencoding words publicReplies selections rows budget required stopAfter (next answer) result.2) := by
  simp only [proposalRun, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
    proposalImpl, OptionT.run_mk, StateT.run_mk]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨answer, after⟩
  cases answer <;> rfl

theorem proposalRun_erasure {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ProposalState inputs) :
    Prod.map id Prod.snd <$>
        proposalRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state =
      monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state.2 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [proposalRun_pure, monitoredRun_pure, map_pure]; rfl
  | query_bind input next ih =>
      rw [proposalRun_query_bind, map_bind, monitoredRun_query_bind,
        ← proposalStep_erasure key inputs hencoding words publicReplies selections rows budget required stopAfter input state,
        bind_map_left]
      apply RetainedObservation.bind_congr
      rintro ⟨answer, after⟩ _
      cases answer with
      | none => simp only [Option.elim_none, map_pure]; rfl
      | some answer => exact ih answer after

theorem proposalRun_complete {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ProposalState inputs) (hvalid : MonitoredValid inputs state.2)
    (hinputs : sourceInputs key computation ⊆ inputs) (total : Nat) :
    (proposalRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state >>= fun result =>
      (liftM (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) : SPMF (List Index))) =
      (liftM (completeProposalWord (PMF.uniformOfFintype Index) total state.1) : SPMF (List Index)) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rw [proposalRun_pure, pure_bind]
  | query_bind input next ih =>
      rw [proposalRun_query_bind, bind_assoc]
      calc
        _ = proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state >>= fun result =>
            (liftM (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) : SPMF (List Index)) := by
          apply RetainedObservation.bind_congr
          intro result hresult
          have hafter := proposalStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter
            input state hvalid result hresult
          rcases result with ⟨answer, after⟩
          cases answer with
          | none => rw [Option.elim_none, pure_bind]
          | some answer =>
              exact ih answer after hafter ((sourceInputs_next_subset key input next answer).trans hinputs)
        _ = _ := proposalStep_complete key inputs hencoding words publicReplies selections rows budget required stopAfter
          input state ((requestInputs_subset key input next).trans hinputs) hvalid total

theorem expected_proposalRun_terminalPotential {Result : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : ProposalState inputs)
    (hvalid : MonitoredValid inputs state.2) (hinputs : sourceInputs key computation ⊆ inputs)
    (total : Nat) (payoff : List Index → ENNReal) :
    (∑' result, Pr[= result |
        proposalRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] *
      terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) =
        terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
  have h := congrArg (fun law : SPMF (List Index) => ∑' word, Pr[= word | law] * payoff word)
    (proposalRun_complete key inputs hencoding words publicReplies selections rows budget required stopAfter computation state hvalid hinputs total)
  rw [tsum_probOutput_bind_mul] at h
  simpa only [terminalProposalPotential, SPMF.probOutput_liftM] using h

end SphincsSecurity.Concrete.RetainedResidual
