import SphincsSecurity.Proof.Forced.FtsGuessTracking
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec OtsContactTrace
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State Environment fixedRun fixedImpl runWith)
set_option backward.isDefEq.respectTransparency false

variable {Memory : Type}

private theorem map_nonzero {First Result : Type} (function : First → Result) (law : SPMF First) (result : Result) :
    (function <$> law) result ≠ 0 ↔ ∃ first, law first ≠ 0 ∧ result = function first := by
  simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]

private theorem logged_query_bind {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) :
    OtsPrefix.logged (liftM ((OracleWorld + SigningSpec).query input) >>= next) =
      liftM ((OracleWorld + SigningSpec).query input) >>= fun answer =>
        (fun tail => (tail.1, signingLogFragment input answer ++ tail.2)) <$> OtsPrefix.logged (next answer) := by
  simp only [OtsPrefix.logged, OtsProbeSimulation.simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    simulateQ_id', OtsProbeSimulation.signingTraceComputation_query_bind]

private theorem adversaryRun_pure {Result : Type} (parameter : PublicParameter) (labels : CanonicalGraphLabels) (result : Result) :
    adversaryRun parameter labels (pure result) = pure (((result, []), 1), 1) := by
  simp only [adversaryRun, OtsPrefix.logged, simulateQ_pure, WriterT.run_pure]
  rfl

private theorem adversaryRun_query_bind {Result : Type} (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) :
    adversaryRun parameter labels (liftM ((OracleWorld + SigningSpec).query input) >>= next) = (do
      let head ← ((adversaryImpl parameter labels input).run).run
      let tail ← adversaryRun parameter labels (next head.1.1)
      pure (((tail.1.1.1, signingLogFragment input head.1.1 ++ tail.1.1.2), head.1.2 * tail.1.2), head.2 * tail.2)) := by
  simp only [adversaryRun, logged_query_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_map,
    WriterT.run_bind, WriterT.run_map, Functor.map_map, bind_pure_comp]

theorem fixed_adversaryRun_tracking (environment : Environment Auxiliary Coordinate Digest Memory) (key : SecretKey)
    (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (hsigning : ∀ message state result,
      fixedRun environment (FtsGuessSigning.secretTable key.ftsSecret) (signingProgram message) state result ≠ 0 →
      ∀ signature, result.1.1.1 = some signature →
        result.1.1.2 = some (RetainedResidual.signingView key f message signature))
    {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : State Coordinate Digest Memory)
    (result : (((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace) × State Coordinate Digest Memory)
    (hr : fixedRun environment (FtsGuessSigning.secretTable key.ftsSecret) (adversaryRun key.parameter labels computation) state result ≠ 0) :
    Tracking key f state result.2 result.1.1.1.2 result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [adversaryRun_pure, fixedRun, SecretGuessObservation.runWith_pure,
        ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact Tracking.refl key f state
  | query_bind input next ih =>
      simp only [adversaryRun_query_bind, fixedRun, runWith_bind, SecretGuessObservation.runWith_pure,
        RetainedObservation.bind_nonzero, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      obtain ⟨head, hh, tail, ht, rfl⟩ := hr
      have hhead : Tracking key f state head.2 (signingLogFragment input head.1.1.1) head.1.2 := by
        cases input with
        | inl input =>
            simp only [adversaryImpl, WriterT.run_mk, runWith_map, map_nonzero] at hh
            obtain ⟨answer, ha, rfl⟩ := hh
            exact fixed_worldProgram_tracking environment key f labels input state answer ha
        | inr message =>
            simp only [adversaryImpl, WriterT.run_mk, runWith_map, map_nonzero] at hh
            obtain ⟨record, hr, rfl⟩ := hh
            exact fixed_signingProgram_tracking environment key f message state record hr (hsigning message state record hr)
      exact hhead.trans (ih head.1.1.1 head.2 tail ht)

private theorem traced_map {First Result : Type} (function : First → Result) (computation : OracleComp OracleWorld First) :
    QueryPause.traced hashObservationTrace (function <$> computation) =
      (fun result => (function result.1, result.2)) <$> QueryPause.traced hashObservationTrace computation := by
  simp only [QueryPause.traced, simulateQ_map, WriterT.run_map]

theorem fixed_tracedBoundary_tracking (environment : Environment Auxiliary Coordinate Digest Memory) (key : SecretKey)
    (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    {Result : Type} (computation : OracleComp OracleWorld Result) (state : State Coordinate Digest Memory)
    (result : ((Result × SigningBoundaryTrace) × Trace) × State Coordinate Digest Memory)
    (hr : fixedRun environment (FtsGuessSigning.secretTable key.ftsSecret) (simulateQ (worldProgram key.parameter labels)
      (QueryPause.traced hashObservationTrace (boundaryComputation key.parameter computation))) state result ≠ 0) :
    Tracking key f state result.2 [] result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [boundaryComputation, simulateQ_pure, WriterT.run_pure, QueryPause.traced_pure,
        fixedRun, SecretGuessObservation.runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact Tracking.refl key f state
  | query_bind input next ih =>
      simp only [ResidualByteFrontend.boundaryComputation_query_bind, QueryPause.traced_query_bind, traced_map,
        simulateQ_bind, simulateQ_spec_query, simulateQ_map, fixedRun, runWith_bind, runWith_map,
        RetainedObservation.bind_nonzero, map_nonzero] at hr
      obtain ⟨middle, hm, outer, ⟨tail, ht, rfl⟩, rfl⟩ := hr
      exact (fixed_worldProgram_tracking environment key f labels input state middle hm).trans
        (ih middle.1 middle.2 tail ht)

theorem fixed_completedRun_tracking (environment : Environment Auxiliary Coordinate Digest Memory) (key : SecretKey)
    (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (hsigning : ∀ message state result,
      fixedRun environment (FtsGuessSigning.secretTable key.ftsSecret) (signingProgram message) state result ≠ 0 →
      ∀ signature, result.1.1.1 = some signature →
        result.1.1.2 = some (RetainedResidual.signingView key f message signature))
    (adversary : Adversary) (state : State Coordinate Digest Memory) (result : Completed × State Coordinate Digest Memory)
    (hr : fixedRun environment (FtsGuessSigning.secretTable key.ftsSecret)
      (completedRun key.parameter key.root labels adversary) state result ≠ 0) :
    Tracking key f state result.2 result.1.1.1.1.2 (result.1.1.2 * result.1.2.2) := by
  simp only [completedRun, fixedRun, runWith_bind, SecretGuessObservation.runWith_pure,
    RetainedObservation.bind_nonzero, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  obtain ⟨before, hb, checked, hc, rfl⟩ := hr
  have hbefore := fixed_adversaryRun_tracking environment key f labels hsigning _ state before hb
  have hchecked := fixed_tracedBoundary_tracking environment key f labels _ before.2 checked hc
  simpa only [List.append_nil] using hbefore.trans hchecked

theorem Tracking.uncovered_guess {key : SecretKey} {f : QueryImpl HashSpec Id} {before after : State Coordinate Digest Memory}
    {log : QueryLog SigningSpec} {trace : Trace} (tracking : Tracking key f before after log trace)
    (target : FewTimeView) (tree : FtsTree) (hinitial : (target.1, tree, target.2 tree) ∉ before.retired)
    (hcovered : ¬ReferenceFtsCoverage.CoveredByLog key f log target tree)
    (hquery : FtsVerifierWitness.TrueSecretQuery f key target.1 tree (target.2 tree) trace) :
    (target.1, tree, target.2 tree) ∈ after.guesses := by
  rcases tracking.origin (target.1, tree, target.2 tree) (tracking.queried _ hquery) with h | h | h
  · exact (hinitial h).elim
  · exact h
  · exact (hcovered h).elim

theorem Tracking.two_guesses {key : SecretKey} {f : QueryImpl HashSpec Id} {before after : State Coordinate Digest Memory}
    {log : QueryLog SigningSpec} {trace : Trace} (tracking : Tracking key f before after log trace)
    (hinitial : before.retired = ∅) (forgery : Forgery) (h : ReferenceFtsCoverage.TwoGuesses key f log trace forgery) :
    2 ≤ after.guesses.card := by
  obtain ⟨first, second, hne, hf, hqf, hs, hqs⟩ := h
  let target := RetainedResidual.signingView key f forgery.message forgery.signature
  have hf := tracking.uncovered_guess target first (by rw [hinitial]; exact Finset.notMem_empty _) hf hqf
  have hs := tracking.uncovered_guess target second (by rw [hinitial]; exact Finset.notMem_empty _) hs hqs
  exact Finset.one_lt_card.mpr ⟨_, hf, _, hs, fun he => hne (congrArg (fun c : Coordinate => c.2.1) he)⟩

theorem Tracking.near_guess {key : SecretKey} {f : QueryImpl HashSpec Id} {before after : State Coordinate Digest Memory}
    {log : QueryLog SigningSpec} {trace : Trace} (tracking : Tracking key f before after log trace)
    (hinitial : before.retired = ∅) (boundary : SigningBoundaryTrace) (forgery : Forgery)
    (h : ReferenceFtsCoverage.NearGuess key f log boundary trace forgery) :
    let target := RetainedResidual.signingView key f forgery.message forgery.signature
    ∃ omitted, TargetCertificateAt key (Finset.univ.erase omitted)
      (ReferenceFtsCoverage.transcriptCache f boundary trace, log) (RetainedResidual.signingInput key forgery.message forgery.signature) ∧
      (target.1, omitted, target.2 omitted) ∈ after.guesses := by
  obtain ⟨omitted, hcertificate, hcovered, hquery⟩ := h
  exact ⟨omitted, hcertificate, tracking.uncovered_guess _ omitted
    (by rw [hinitial]; exact Finset.notMem_empty _) hcovered hquery⟩

end SphincsSecurity.Concrete.FtsGuessHash
