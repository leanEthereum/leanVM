import SphincsSecurity.Proof.Residual.RetainedResidualMonitorStops
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
set_option backward.isDefEq.respectTransparency false

abbrev ExceptionHistoryState (inputs : Finset HashInput) := MonitoredState inputs × (Bool × Bool)

noncomputable def exceptionHistoryUpdate {inputs : Finset HashInput} (key : SecretKey)
    (before after : MonitoredState inputs) (history : Bool × Bool) : Bool × Bool :=
  (history.1 || decide (CertificateCacheExceptional key before.1.memory.external.cache) ||
    decide (CertificateCacheExceptional key after.1.memory.external.cache),
   history.2 || decide (ProposalPrefixExceptional after.2.proposals after.2.log.length))

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

noncomputable def exceptionHistoryStep (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionHistoryState inputs) :
    SPMF (Option ((OracleWorld + SigningSpec).Range input) × ExceptionHistoryState inputs) :=
  (fun result => (result.1, result.2, exceptionHistoryUpdate key state.1 result.2 state.2)) <$>
    monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1

noncomputable def exceptionHistoryRun {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) : SPMF (Option Result × ExceptionHistoryState inputs) :=
  (simulateQ (fun input => OptionT.mk (StateT.mk
    (exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input))) computation).run.run state

theorem exceptionHistoryStep_erasure (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionHistoryState inputs) :
    (fun result => (result.1, result.2.1)) <$>
      exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state =
      monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1 := by
  simp only [exceptionHistoryStep, Functor.map_map]
  exact id_map _

theorem exceptionHistoryStep_support (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionHistoryState inputs)
    (result : Option ((OracleWorld + SigningSpec).Range input) × ExceptionHistoryState inputs)
    (hresult : exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1 (result.1, result.2.1) ≠ 0 ∧
      result.2.2 = exceptionHistoryUpdate key state.1 result.2.1 state.2 := by
  obtain ⟨raw, hraw, heq⟩ := map_nonzero_source _ _ _ hresult
  cases heq
  exact ⟨hraw, rfl⟩

theorem exceptionHistoryRun_pure {Result : Type} (value : Result) (state : ExceptionHistoryState inputs) :
    exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter (pure value) state =
      pure (some value, state) := by
  simp only [exceptionHistoryRun, simulateQ_pure, OptionT.run_pure, StateT.run_pure]

theorem exceptionHistoryRun_query_bind {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) :
    exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
      (exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state >>= fun result =>
        result.1.elim (pure (none, result.2)) fun answer =>
          exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter (next answer) result.2) := by
  simp only [exceptionHistoryRun, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
    OptionT.run_mk, StateT.run_mk]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨answer, after⟩
  cases answer <;> rfl

theorem exceptionHistoryRun_erasure {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) :
    (fun result => (result.1, result.2.1)) <$>
      exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state =
      monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [exceptionHistoryRun_pure, map_pure, monitoredRun_pure]
  | query_bind input next ih =>
      rw [exceptionHistoryRun_query_bind, map_bind, monitoredRun_query_bind,
        ← exceptionHistoryStep_erasure key inputs hencoding words publicReplies selections rows budget required stopAfter input state,
        bind_map_left]
      apply RetainedObservation.bind_congr
      rintro ⟨answer, after⟩ _
      cases answer with
      | none => simp only [Option.elim_none, map_pure]
      | some answer => exact ih answer after

theorem exceptionHistoryRun_support {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) (result : Option Result × ExceptionHistoryState inputs)
    (hresult : exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state result ≠ 0) :
    monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state.1 (result.1, result.2.1) ≠ 0 := by
  have h := map_nonzero _ (fun result => (result.1, result.2.1)) result hresult
  rwa [exceptionHistoryRun_erasure] at h

theorem exceptionHistoryRun_clean {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) (result : Option Result × ExceptionHistoryState inputs)
    (hresult : exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state result ≠ 0)
    (hclean : result.2.2 = (false, false)) : state.2 = (false, false) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [exceptionHistoryRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hclean
  | query_bind input next ih =>
      rw [exceptionHistoryRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, after⟩, hstep, hresult⟩ := hresult
      have hafter : after.2 = (false, false) := by
        cases answer with
        | none =>
            simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
            subst result
            exact hclean
        | some answer => exact ih answer after hresult
      have hupdate := (exceptionHistoryStep_support key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state (answer, after) hstep).2
      rw [hupdate] at hafter
      simp only [exceptionHistoryUpdate, Prod.mk.injEq, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hafter
      exact Prod.ext hafter.1.1.1 hafter.2.1

end SphincsSecurity.Concrete.RetainedResidual
