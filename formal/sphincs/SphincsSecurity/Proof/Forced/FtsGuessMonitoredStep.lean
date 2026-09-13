import SphincsSecurity.Proof.Forced.FtsGuessInputCoverage
import SphincsSecurity.Proof.Residual.RetainedResidualMonitoredStep
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion OtsContactTrace
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State)
open RetainedResidual (proposalOfSigningRecord proposalOfWorldResult signingAnnotation)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput hashInputs

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)

theorem cachedForcedRun_map {First Result : Type} (function : First → Result) (computation : OracleComp World First)
    (state : CachedState) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (function <$> computation) state =
      (fun result => (function result.1, result.2)) <$>
        cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot computation state := by
  simp only [cachedForcedRun, simulateQ_map, StateT.run_map]

/-! ### The adversary run, one query at a time -/

abbrev AdversaryStep (input : (OracleWorld + SigningSpec).Domain) :=
  ((OracleWorld + SigningSpec).Range input × SigningBoundaryTrace) × Trace

def combineStep {Result : Type} (input : (OracleWorld + SigningSpec).Domain) (step : AdversaryStep input)
    (tail : ((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace) :
    ((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace :=
  (((tail.1.1.1, signingLogFragment input step.1.1 ++ tail.1.1.2), step.1.2 * tail.1.2), step.2 * tail.2)

theorem adversaryRun_pure {Result : Type} (value : Result) :
    adversaryRun parameter labels (pure value) = pure (((value, []), 1), 1) := by
  simp only [adversaryRun, logged_eq_signingTrace, FtsProbeSimulation.signingTraceComputation, OracleComp.construct_pure,
    simulateQ_pure, WriterT.run_pure]

theorem adversaryRun_query_bind {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) :
    adversaryRun parameter labels (liftM ((OracleWorld + SigningSpec).query input) >>= next) =
      ((adversaryImpl parameter labels input).run.run >>= fun step =>
        combineStep input step <$> adversaryRun parameter labels (next step.1.1)) := by
  simp only [adversaryRun, logged_eq_signingTrace, FtsProbeSimulation.signingTraceComputation_query_bind, simulateQ_bind,
    simulateQ_spec_query, simulateQ_map, WriterT.run_bind, WriterT.run_map, Functor.map_map]
  rfl

noncomputable def forcedAdversaryStep (input : (OracleWorld + SigningSpec).Domain) (state : CachedState) :
    SPMF (AdversaryStep input × CachedState) :=
  cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
    ((adversaryImpl parameter labels input).run.run) state

theorem cachedForcedRun_adversaryRun_pure {Result : Type} (value : Result) (state : CachedState) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (adversaryRun parameter labels (pure value)) state = pure ((((value, []), 1), 1), state) := by
  rw [adversaryRun_pure, cachedForcedRun_pure]

theorem cachedForcedRun_adversaryRun_query_bind {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) (state : CachedState) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (adversaryRun parameter labels (liftM ((OracleWorld + SigningSpec).query input) >>= next)) state =
      (forcedAdversaryStep parameter root otsSecret labels inputs hencoding selections rows dummy slot input state >>= fun step =>
        (fun tail => (combineStep input step.1 tail.1, tail.2)) <$>
          cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
            (adversaryRun parameter labels (next step.1.1.1)) step.2) := by
  rw [adversaryRun_query_bind, cachedForcedRun_bind]
  apply congrArg (_ >>= ·)
  funext step
  rw [cachedForcedRun_map]

theorem forcedAdversaryStep_world (input : OracleWorld.Domain) (state : CachedState) :
    forcedAdversaryStep parameter root otsSecret labels inputs hencoding selections rows dummy slot (.inl input) state =
      (fun result => (((result.1, signingBoundaryTrace parameter input result.1), hashObservationTrace input result.1), result.2)) <$>
        cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (worldProgram parameter labels input) state := by
  rw [forcedAdversaryStep]
  simp only [adversaryImpl, WriterT.run_mk]
  rw [cachedForcedRun_map]
  rfl

theorem forcedAdversaryStep_sign (message : Message) (state : CachedState) :
    forcedAdversaryStep parameter root otsSecret labels inputs hencoding selections rows dummy slot (.inr message) state =
      (fun result => (((result.1.1.1, result.1.2), 1), result.2)) <$>
        cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (signingProgram message) state := by
  rw [forcedAdversaryStep]
  simp only [adversaryImpl, WriterT.run_mk]
  rw [cachedForcedRun_map]

/-! ### The passive certificate monitor -/

abbrev MonitoredState := CachedState × CertificateMonitor

def monitorView (state : MonitoredState) : CertificateMonitorState := (state.1.1, state.2)

def monitorKey : SecretKey := ⟨parameter, root, fun _ _ _ _ => 0, fun _ _ _ => 0⟩

variable (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

noncomputable def monitoredWorldStep (input : OracleWorld.Domain) (state : MonitoredState) :
    SPMF (AdversaryStep (.inl input) × MonitoredState) :=
  (fun result => (((result.1, signingBoundaryTrace parameter input result.1), hashObservationTrace input result.1),
    (result.2, certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter (.inl input) (monitorView state) 0
      (proposalOfWorldResult parameter input (result.1, result.2.1))))) <$>
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (worldProgram parameter labels input) state.1

noncomputable def monitoredSignStep (message : Message) (state : MonitoredState) :
    SPMF (AdversaryStep (.inr message) × MonitoredState) :=
  (liftM (signingAnnotation (monitorKey parameter root) budget message (monitorView state)) : SPMF _) >>= fun annotation =>
    (fun result => (((result.1.1.1, result.1.2), 1),
      (result.2, certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter (.inr message) (monitorView state) annotation.1
        (proposalOfSigningRecord message result.1 result.2.1 (result.1.1.2.elim annotation.2 Prod.fst))))) <$>
      cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (signingProgram message) state.1

noncomputable def monitoredStep : (input : (OracleWorld + SigningSpec).Domain) → MonitoredState →
    SPMF (AdversaryStep input × MonitoredState)
  | .inl input, state => monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state
  | .inr message, state => monitoredSignStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter message state

theorem monitoredStep_erasure (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState) :
    (fun result => (result.1, result.2.1)) <$>
      monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state =
      forcedAdversaryStep parameter root otsSecret labels inputs hencoding selections rows dummy slot input state.1 := by
  cases input with
  | inl input =>
      rw [monitoredStep, monitoredWorldStep, forcedAdversaryStep_world, Functor.map_map]
  | inr message =>
      rw [monitoredStep, monitoredSignStep, forcedAdversaryStep_sign, map_bind]
      refine (RetainedObservation.bind_congr _ _ _ (fun annotation _ => ?_)).trans (RetainedObservation.lift_bind_const _ _)
      rw [Functor.map_map]

/-! ### Monitored runs -/

noncomputable def monitoredRun {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    MonitoredState → SPMF ((((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace) × MonitoredState) :=
  OracleComp.construct (fun value state => pure ((((value, []), 1), 1), state))
    (fun input _ next state =>
      monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>= fun step =>
        (fun tail => (combineStep input step.1 tail.1, tail.2)) <$> next step.1.1.1 step.2) computation

theorem monitoredRun_pure {Result : Type} (value : Result) (state : MonitoredState) :
    monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (pure value) state =
      pure ((((value, []), 1), 1), state) := rfl

theorem monitoredRun_query_bind {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) (state : MonitoredState) :
    monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
      (monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>= fun step =>
        (fun tail => (combineStep input step.1 tail.1, tail.2)) <$>
          monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (next step.1.1.1) step.2) := by
  rw [monitoredRun, OracleComp.construct_query_bind]
  rfl

theorem monitoredRun_erasure {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : MonitoredState) :
    (fun result => (result.1, result.2.1)) <$>
      monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state =
      cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (adversaryRun parameter labels computation) state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rw [monitoredRun_pure, cachedForcedRun_adversaryRun_pure, map_pure]
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, cachedForcedRun_adversaryRun_query_bind, map_bind, ← monitoredStep_erasure, bind_map_left]
      apply congrArg (_ >>= ·)
      funext step
      rw [Functor.map_map, ← ih step.1.1.1 step.2, Functor.map_map]

noncomputable def monitoredWorldRun {Result : Type} (computation : OracleComp OracleWorld Result) :
    MonitoredState → SPMF (((Result × SigningBoundaryTrace) × Trace) × MonitoredState) :=
  OracleComp.construct (fun value state => pure (((value, 1), 1), state))
    (fun input _ next state =>
      monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>= fun step =>
        (fun tail => (((tail.1.1.1, step.1.1.2 * tail.1.1.2), step.1.2 * tail.1.2), tail.2)) <$> next step.1.1.1 step.2) computation

theorem monitoredWorldRun_pure {Result : Type} (value : Result) (state : MonitoredState) :
    monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (pure value) state =
      pure (((value, 1), 1), state) := rfl

theorem monitoredWorldRun_query_bind {Result : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld Result) (state : MonitoredState) :
    monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (liftM (OracleWorld.query input) >>= next) state =
      (monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>= fun step =>
        (fun tail => (((tail.1.1.1, step.1.1.2 * tail.1.1.2), step.1.2 * tail.1.2), tail.2)) <$>
          monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (next step.1.1.1) step.2) := by
  rw [monitoredWorldRun, OracleComp.construct_query_bind]
  rfl

theorem traced_map {First Result : Type} (function : First → Result) (computation : OracleComp OracleWorld First) :
    QueryPause.traced hashObservationTrace (function <$> computation) =
      (fun result => (function result.1, result.2)) <$> QueryPause.traced hashObservationTrace computation := by
  simp only [QueryPause.traced, simulateQ_map, WriterT.run_map]

noncomputable def tracedWorldProgram {Result : Type} (computation : OracleComp OracleWorld Result) :
    OracleComp World ((Result × SigningBoundaryTrace) × Trace) :=
  simulateQ (worldProgram parameter labels) (QueryPause.traced hashObservationTrace (boundaryComputation parameter computation))

theorem tracedWorldProgram_pure {Result : Type} (value : Result) :
    tracedWorldProgram parameter labels (pure value) = pure ((value, 1), 1) := by
  simp only [tracedWorldProgram, boundaryComputation, simulateQ_pure, WriterT.run_pure, QueryPause.traced_pure]

theorem tracedWorldProgram_query_bind {Result : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld Result) :
    tracedWorldProgram parameter labels (liftM (OracleWorld.query input) >>= next) =
      (worldProgram parameter labels input >>= fun answer =>
        (fun tail => ((tail.1.1, signingBoundaryTrace parameter input answer * tail.1.2), hashObservationTrace input answer * tail.2)) <$>
          tracedWorldProgram parameter labels (next answer)) := by
  simp only [tracedWorldProgram, ResidualByteFrontend.boundaryComputation_query_bind, QueryPause.traced_query_bind, traced_map,
    simulateQ_bind, simulateQ_spec_query, simulateQ_map, Functor.map_map]

theorem verifyProgram_eq_traced (forgery : Forgery) :
    verifyProgram parameter root labels forgery =
      tracedWorldProgram parameter labels (liftM (verify ⟨root, parameter⟩ forgery.message forgery.signature : OracleComp HashSpec Bool)) := rfl

theorem monitoredWorldStep_erasure (input : OracleWorld.Domain) (state : MonitoredState) :
    (fun result => (result.1, result.2.1)) <$>
      monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state =
      (fun result => (((result.1, signingBoundaryTrace parameter input result.1), hashObservationTrace input result.1), result.2)) <$>
        cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (worldProgram parameter labels input) state.1 := by
  rw [monitoredWorldStep, Functor.map_map]

theorem cachedForcedRun_tracedWorldProgram_query_bind {Result : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld Result) (state : CachedState) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (tracedWorldProgram parameter labels (liftM (OracleWorld.query input) >>= next)) state =
      (((fun result => (((result.1, signingBoundaryTrace parameter input result.1), hashObservationTrace input result.1), result.2)) <$>
        cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (worldProgram parameter labels input) state) >>=
        fun step => (fun tail => (((tail.1.1.1, step.1.1.2 * tail.1.1.2), step.1.2 * tail.1.2), tail.2)) <$>
          cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
            (tracedWorldProgram parameter labels (next step.1.1.1)) step.2) := by
  rw [tracedWorldProgram_query_bind, cachedForcedRun_bind, bind_map_left]
  apply congrArg (_ >>= ·)
  funext step
  rw [cachedForcedRun_map]

theorem monitoredWorldRun_erasure {Result : Type} (computation : OracleComp OracleWorld Result) (state : MonitoredState) :
    (fun result => (result.1, result.2.1)) <$>
      monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state =
      cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
        (tracedWorldProgram parameter labels computation) state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rw [monitoredWorldRun_pure, tracedWorldProgram_pure, cachedForcedRun_pure, map_pure]
  | query_bind input next ih =>
      rw [monitoredWorldRun_query_bind, cachedForcedRun_tracedWorldProgram_query_bind, map_bind, ← monitoredWorldStep_erasure,
        bind_map_left]
      apply congrArg (_ >>= ·)
      funext step
      rw [Functor.map_map, ← ih step.1.1.1 step.2, Functor.map_map]

noncomputable def monitoredCompletedRun (adversary : Adversary) (state : MonitoredState) : SPMF (Completed × MonitoredState) :=
  monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    (adversary.main ⟨root, parameter⟩) state >>= fun before =>
    (fun checked => ((before.1, checked.1), checked.2)) <$>
      monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (liftM (verify ⟨root, parameter⟩ before.1.1.1.1.message before.1.1.1.1.signature : OracleComp HashSpec Bool)) before.2

theorem monitoredCompletedRun_erasure (adversary : Adversary) (state : MonitoredState) :
    (fun result => (result.1, result.2.1)) <$>
      monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter adversary state =
      cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
        (completedRun parameter root labels adversary) state.1 := by
  rw [monitoredCompletedRun, completedRun, cachedForcedRun_bind, map_bind, ← monitoredRun_erasure, bind_map_left]
  apply congrArg (_ >>= ·)
  funext before
  rw [cachedForcedRun_bind, Functor.map_map, verifyProgram_eq_traced, ← monitoredWorldRun_erasure, bind_map_left]
  simp only [cachedForcedRun_pure, map_eq_bind_pure_comp, Function.comp_def]
  rfl

end SphincsSecurity.Concrete.FtsGuessHash
