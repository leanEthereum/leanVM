import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualMonitoredStep

/-! ## RetainedResidualMessageHistory -/

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyRun_rowsCovered {Result : Type} (computation : OracleComp (World inputs) Result) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (result : Option Result × State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows) computation state result ≠ 0) :
    ResidualByteFrontend.RowsCovered inputs (project result.2) := by
  rw [← run_erasure _ _ state ha, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨actual, _, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨seed, _, hresult⟩ := hresult
  exact observedRun_rowsCovered parameter inputs hencoding words publicReplies selections rows actual seed computation state hcovered result hresult

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyRun_record_bind {Result : Type} (message : Message) (record : SigningRecord)
    (next : Unit → OracleComp (World inputs) Result) (state : State inputs) :
    lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (recordSigning inputs message record >>= next) state =
      lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (next ()) { state with memory := state.memory.recordSigning message record } := by
  rw [recordSigning, lazyRun, runWith_query_bind]
  simp only [lazyImpl, environment, OptionT.run_mk, StateT.run_mk, SPMF.lift_pure, pure_bind, Option.elim_some, lazyRun]

theorem lazyRun_signingProgram (message : Message) (state : State inputs) :
    lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (signingProgram inputs key.parameter key.root words selections message) state =
      (fun result : Option SigningRecord × State inputs => result.1.elim (none, result.2) fun record =>
        (some record.1.1, { result.2 with memory := result.2.memory.recordSigning message record })) <$>
        lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
          (simulateQ (embed inputs state.memory.routing)
            (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state := by
  rw [signingProgram, lazyRun_routing_bind, lazyRun_bind, map_eq_bind_pure_comp]
  apply RetainedObservation.bind_congr
  rintro ⟨answer, after⟩ _
  cases answer with
  | none => rfl
  | some record =>
      rw [Option.elim_some, lazyRun_record_bind]
      exact runWith_pure _ _ _

variable (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem monitoredStep_erasure (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs) :
    (fun result => (result.1, result.2.1)) <$>
      monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state =
      lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (adversaryImpl inputs key.parameter key.root words selections input) state.1 := by
  cases input with
  | inl input =>
      rw [monitoredStep, Functor.map_map]
      change id <$> _ = _
      rw [id_map]
      rfl
  | inr message =>
      rw [monitoredStep, map_bind]
      calc
        _ = (liftM (signingAnnotation key budget message (monitorView state)) : SPMF _) >>= fun _ =>
            lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
              (signingProgram inputs key.parameter key.root words selections message) state.1 := by
          apply RetainedObservation.bind_congr
          intro annotation _
          rw [Functor.map_map, lazyRun_signingProgram]
          congr 1
          funext result
          rcases result with ⟨answer, after⟩
          cases answer <;> rfl
        _ = _ := RetainedObservation.lift_bind_const _ _

def MonitoredValid (state : MonitoredState inputs) : Prop :=
  (∀ coordinate, (state.1.candidates coordinate).Nonempty) ∧ ResidualByteFrontend.RowsCovered inputs (project state.1)

theorem monitoredStep_valid (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    MonitoredValid inputs result.2 := by
  have h := map_nonzero _ (fun result => (result.1, result.2.1)) result hresult
  rw [monitoredStep_erasure] at h
  exact ⟨lazyRun_nonempty _ _ state.1 hvalid.1 _ h,
    lazyRun_rowsCovered key.parameter inputs hencoding words publicReplies selections rows _ state.1 hvalid.1 hvalid.2 _ h⟩

noncomputable def monitoredRun {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) : SPMF (Option Result × MonitoredState inputs) :=
  (simulateQ (monitoredImpl key inputs hencoding words publicReplies selections rows budget required stopAfter) computation).run.run state

theorem monitoredRun_pure {Result : Type} (value : Result) (state : MonitoredState inputs) :
    monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter (pure value) state =
      pure (some value, state) := by
  simp only [monitoredRun, simulateQ_pure, OptionT.run_pure, StateT.run_pure]

theorem monitoredRun_query_bind {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) :
    monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
      (monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state >>= fun result =>
        result.1.elim (pure (none, result.2)) fun answer =>
          monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter (next answer) result.2) := by
  simp only [monitoredRun, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
    monitoredImpl, OptionT.run_mk, StateT.run_mk]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨answer, after⟩
  cases answer <;> rfl

theorem monitoredRun_erasure {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) :
    (fun result => (result.1, result.2.1)) <$>
      monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state =
      lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation) state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [monitoredRun_pure, map_pure, simulateQ_pure, lazyRun, runWith_pure]
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query, lazyRun_bind,
        ← monitoredStep_erasure key inputs hencoding words publicReplies selections rows budget required stopAfter input state,
        bind_map_left]
      apply RetainedObservation.bind_congr
      rintro ⟨answer, after⟩ _
      cases answer with
      | none => simp only [Option.elim_none, map_pure]
      | some answer => exact ih answer after

end SphincsSecurity.Concrete.RetainedResidual
