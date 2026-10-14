import Whir.SpongefishCurrentReplayProvenance
import Whir.SpongefishCurrentSourceCallerOriginal
import Whir.PCSBCSMixedConstructionTrace

/-! Actual current replay provenance and public-answer completeness. Compiler
cache entries and returned bytes have literal earlier construction observations,
including rejected prefixes. Counts bounds the keys of this execution, not the
unobserved keys of other raw-record candidates. No oracle is consulted by the
public parser. `SpongefishCurrentAcceptedJoin` derives the parser's call order,
domain and byte transport from accepted receive and binding; native equation
acceptance remains a separate source interface. -/
namespace Whir.SpongefishCurrentCallerGetterCoverage
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishPCSRoundFrames SpongefishCurrentModeQueries
open SpongefishCurrentMixedModeCompiler SpongefishCurrentReplayProvenance
set_option autoImplicit false
set_option maxRecDepth 10000

/-- A cached full digest is backed by a literal construction observation in the
already completed chronological prefix, not by a coordinate-only certificate. -/
def Recorded (cache : Cache) (past : List Observation) : Prop :=
  ∀ q d, cache q = some d → ∃ valid, (⟨.construction q valid,d⟩ : Observation) ∈ past

def ConstructionTrace (os : List Observation) : Prop :=
  ∀ o ∈ os, ∃ q valid, o.query = .construction q valid

def ByteRecorded (m : Pending) (past : List Observation) (p : Nat) (b : Byte) : Prop :=
  ∃ d valid, (⟨.construction (coordinate m (p/32)) valid,d⟩ : Observation) ∈ past ∧
    b = d ⟨p%32,Nat.mod_lt _ (by decide)⟩

def resultCache : Result → Cache
  | .ok cur => cur.cache
  | .error (cur,_) => cur.cache

theorem empty_recorded (past : List Observation) : Recorded (fun _ => none) past := by
  intro q d hit
  cases hit

theorem recorded_mono {cache : Cache} {a b : List Observation}
    (recorded : Recorded cache a) (included : ∀ o ∈ a, o ∈ b) : Recorded cache b := by
  intro q d hit
  obtain ⟨valid,member⟩ := recorded q d hit
  exact ⟨valid,included _ member⟩

theorem store_recorded (cache : Cache) (past : List Observation) (recorded : Recorded cache past)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q) (d : Digest32) :
    Recorded (store cache q d) (past ++ [⟨.construction q valid,d⟩]) := by
  intro other value hit
  unfold store at hit
  split at hit
  · rename_i equal
    subst other
    cases Option.some.inj hit
    exact ⟨valid,List.mem_append_right _ (by simp)⟩
  · obtain ⟨proof,member⟩ := recorded other value hit
    exact ⟨proof,List.mem_append_left _ member⟩

theorem request_recorded (cache : Cache) (past : List Observation)
    (recorded : Recorded cache past) (q : Coordinate) (valid : DuplexEncoding.Admissible q)
    {os : List Observation} {result : Cache × Digest32}
    (ran : Runs (request cache q valid) os result) :
    Recorded result.1 (past ++ os) ∧
      (∃ proof, (⟨.construction q proof,result.2⟩ : Observation) ∈ past ++ os) ∧
      ConstructionTrace os := by
  cases hit : cache q with
  | some d =>
    simp only [request,hit] at ran
    cases ran
    exact ⟨by simpa using recorded,by simpa using recorded q d hit,by simp [ConstructionTrace]⟩
  | none =>
    simp only [request,hit] at ran
    cases ran with
    | ask _ _ d tail =>
      cases tail
      exact ⟨store_recorded cache past recorded q valid d,
        ⟨valid,List.mem_append_right _ (by simp)⟩,by
          intro o member
          simp only [List.mem_singleton] at member
          subst o
          exact ⟨q,valid,rfl⟩⟩

/-- A hit emits no new query; every byte comes from the earlier literal full
answer. This statement also applies to ideal independent-oracle executions. -/
theorem request_hit (cache : Cache) (past : List Observation) (recorded : Recorded cache past)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q) (d : Digest32)
    (hit : cache q = some d) :
    request cache q valid = .done (cache,d) ∧
      ∃ proof, (⟨.construction q proof,d⟩ : Observation) ∈ past := by
  exact ⟨by simp [request,hit],recorded q d hit⟩

theorem collect_recorded (m : Pending) (positions : List Nat)
    (valid : ∀ p ∈ positions, DuplexEncoding.Admissible (coordinate m (p/32)))
    (cache : Cache) (past : List Observation) (recorded : Recorded cache past)
    {os : List Observation} {result : Cache × List Byte}
    (ran : Runs (collect m positions valid cache) os result) :
    Recorded result.1 (past ++ os) ∧
      List.Forall₂ (ByteRecorded m (past ++ os)) positions result.2 ∧ ConstructionTrace os := by
  induction positions generalizing cache past os result with
  | nil =>
    cases ran
    exact ⟨by simpa using recorded,.nil,by simp [ConstructionTrace]⟩
  | cons p ps ih =>
    obtain ⟨first,before,after,trace,requested,rest⟩ := bind_runs _ _ ran
    obtain ⟨last,tail,empty,afterEq,collected,done⟩ := bind_runs _ _ rest
    cases done
    simp only [List.append_nil] at afterEq
    subst after
    obtain ⟨firstRecorded,firstAnswer,firstTrace⟩ := request_recorded cache past recorded
      (coordinate m (p/32)) (valid p List.mem_cons_self) requested
    obtain ⟨lastRecorded,bytesRecorded,tailTrace⟩ := ih _ first.1 (past ++ before)
      firstRecorded collected
    subst os
    refine ⟨by simpa only [List.append_assoc] using lastRecorded,?_,?_⟩
    · obtain ⟨proof,member⟩ := firstAnswer
      apply List.Forall₂.cons
      · refine ⟨first.2,proof,?_,rfl⟩
        simpa only [List.append_assoc] using List.mem_append_left tail member
      · simpa only [List.append_assoc] using bytesRecorded
    · intro o member
      rcases List.mem_append.mp member with member | member
      · exact firstTrace o member
      · exact tailTrace o member

theorem replay_recorded (cur : SemanticCursor) (calls : List Call)
    (past : List Observation) (recorded : Recorded cur.cache past)
    {os : List Observation} {result : Result} (ran : Runs (replayProgram cur calls) os result) :
    Recorded (resultCache result) (past ++ os) ∧ ConstructionTrace os := by
  induction calls generalizing cur past os result with
  | nil =>
    cases ran
    exact ⟨by simpa [resultCache] using recorded,by simp [ConstructionTrace]⟩
  | cons call calls ih =>
    cases call with
    | read kind =>
      simp only [replayProgram] at ran
      cases parsed : kind.codec.parse cur.data.narg with
      | none =>
        simp only [parsed] at ran
        cases ran
        exact ⟨by simpa [resultCache] using recorded,by simp [ConstructionTrace]⟩
      | some pair =>
        obtain ⟨value,rest⟩ := pair
        simp only [parsed] at ran
        exact ih (readNext cur kind value rest) past recorded ran
    | hint =>
      simp only [replayProgram] at ran
      cases hints : cur.data.hints with
      | nil =>
        simp only [hints] at ran
        cases ran
        exact ⟨by simpa [resultCache] using recorded,by simp [ConstructionTrace]⟩
      | cons bytes rest =>
        simp only [hints] at ran
        exact ih (hintNext cur bytes rest) past recorded ran
    | draw g =>
      simp only [replayProgram] at ran
      split at ran
      · exact ih {cur with data := {cur.data with events := cur.data.events ++ [.verifier []]}}
          past recorded ran
      · split at ran
        · obtain ⟨pair,before,after,trace,collected,rest⟩ := bind_runs _ _ ran
          have first := collect_recorded _ _ _ _ past recorded collected
          have last := ih _ (past ++ before) first.1 rest
          subst os
          refine ⟨by simpa only [List.append_assoc] using last.1,?_⟩
          intro o member
          rcases List.mem_append.mp member with member | member
          · exact first.2.2 o member
          · exact last.2 o member
        · cases ran
          exact ⟨by simpa [resultCache] using recorded,by simp [ConstructionTrace]⟩

/-- Empty initial cache and the actual rejecting/succeeding replay discharge
all cache and query-provenance premises internally. -/
theorem initialized_recorded (C : PrimitiveOracle) (iv session : Digest32)
    (instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call) :
    let p := replayProgram (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints) calls
    Recorded (resultCache (runReal C iv p).view.result) (runReal C iv p).view.observations ∧
      ConstructionTrace (runReal C iv p).view.observations := by
  simpa only [List.nil_append] using replay_recorded _ calls [] (empty_recorded [])
    (real_runs C iv _)

/-- Public replay also retains an actual rejected prefix; no success or raw
record candidate is required for completeness of this true tape. -/
theorem replay_getter_complete (C : PrimitiveOracle) (iv session : Digest32)
    (instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call) :
    let p := replayProgram (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints) calls
    let Q := resource (instanceBytes.length+3) calls
    SpongefishCurrentCallerGetter.run
      (SpongefishCurrentCallerGetter.answer (Q := Q) (runReal C iv p).view.observations) p =
        some (runReal C iv p).view.result := by
  apply SpongefishCurrentCallerGetter.run_real
  exact actual_getter C iv _ _ _ (replay_counted _ calls _ (by simp))
    (fun _ h => h) (initialized_recorded C iv session instanceBytes narg hints calls).2

/-- The actual replay suffix is present after the arbitrary attacker prefix and
ordinary constructor queries, before the erased-result return. -/
theorem afterPrefix_replay_included (C : PrimitiveOracle) (iv : Digest32)
    (tag instanceBytes : List Byte) (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (calls : List Call) (nonempty : instanceBytes ≠ []) :
    let input := (runReal C iv prefixProgram).view.result
    let part := replayProgram (SpongefishCurrentInitializedMode.initial
      (SpongefishSessionAdapter.derive (compressionOf C) iv tag) instanceBytes input.narg input.hints) calls
    ∀ o ∈ (runReal C iv part).view.observations,
      o ∈ (runReal C iv (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram calls)).view.observations := by
  dsimp only
  intro o member
  rw [SpongefishCurrentInitializedMode.afterPrefix,bind_real_observations]
  apply List.mem_append_right
  rw [SpongefishCurrentInitializedMode.program,bind_real_observations,
    SpongefishCurrentObservedSessionEntry.setupProgram_nonempty C iv iv tag instanceBytes _ _ nonempty]
  apply List.mem_append_right
  simp only [SpongefishCurrentInitializedMode.constructor_domain,bind_real_observations,
    runReal,List.append_nil]
  exact member

/-- Aggregate Q is derived from the attacker certificate plus the initialized
resource function. No initial-cache, per-key cap or getter premise is supplied. -/
theorem afterPrefix_getter (C : PrimitiveOracle) (iv : Digest32)
    (tag instanceBytes : List Byte) (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (calls : List Call) (A : Nat) (attacker : Counts A prefixProgram) (nonempty : instanceBytes ≠ []) :
    let input := (runReal C iv prefixProgram).view.result
    let part := replayProgram (SpongefishCurrentInitializedMode.initial
      (SpongefishSessionAdapter.derive (compressionOf C) iv tag) instanceBytes input.narg input.hints) calls
    let whole := SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram calls
    let Q := A + SpongefishCurrentInitializedMode.budget tag instanceBytes calls
    ∀ o ∈ (runReal C iv part).view.observations,
      SpongefishCurrentCallerGetter.answer (Q := Q) (runReal C iv whole).view.observations o.query =
        some o.answer := by
  apply actual_getter C iv _ _ _
    (SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes prefixProgram calls A attacker)
    (afterPrefix_replay_included C iv tag instanceBytes prefixProgram calls nonempty)
  exact (initialized_recorded C iv _ instanceBytes _ _ calls).2
/-- Full public-view replay completeness, including exact reached error data.
The actual physical cursor is constructed, not accepted as a saved context. -/
theorem afterPrefix_replay_complete (C : PrimitiveOracle) (iv : Digest32)
    (tag instanceBytes : List Byte) (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (calls : List Call) (A : Nat) (attacker : Counts A prefixProgram) (nonempty : instanceBytes ≠ []) :
    let input := (runReal C iv prefixProgram).view.result
    let session := SpongefishSessionAdapter.derive (compressionOf C) iv tag
    let initial := SpongefishCurrentInitializedMode.initial session instanceBytes input.narg input.hints
    let whole := SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram calls
    let Q := A + SpongefishCurrentInitializedMode.budget tag instanceBytes calls
    (SpongefishCurrentCallerGetter.run
      (SpongefishCurrentCallerGetter.answer (Q := Q) (runReal C iv whole).view.observations)
      (replayProgram initial calls)).map eraseResult =
        some (forgetResult (SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C)
          (SpongefishCurrentObservedSessionEntry.cursor session instanceBytes input.narg input.hints
            (absorb (compressionOf C) (SpongefishSessionAdapter.init (compressionOf C) iv session) instanceBytes)) calls)) := by
  dsimp only
  rw [SpongefishCurrentCallerGetter.run_real C iv _ _
    (afterPrefix_getter C iv tag instanceBytes prefixProgram calls A attacker nonempty),
    Option.map_some]
  exact congrArg some (replay_real C iv _ _ rfl
    (session_bridge (compressionOf C) iv _ instanceBytes)
    (by intro q d found; cases found) calls)


/-- Internally obtained provenance of *all* cached digests at the actual reached
cursor (including errors), with their aggregate bounded raw keys and literal
public getter equality. Replayed bytes need no fresh oracle query. -/
theorem afterPrefix_cached_getter (C : PrimitiveOracle) (iv : Digest32)
    (tag instanceBytes : List Byte) (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (calls : List Call) (A : Nat) (attacker : Counts A prefixProgram) (nonempty : instanceBytes ≠ []) :
    let input := (runReal C iv prefixProgram).view.result
    let part := replayProgram (SpongefishCurrentInitializedMode.initial
      (SpongefishSessionAdapter.derive (compressionOf C) iv tag) instanceBytes input.narg input.hints) calls
    let whole := SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram calls
    let Q := A + SpongefishCurrentInitializedMode.budget tag instanceBytes calls
    ∀ q d, resultCache (runReal C iv part).view.result q = some d →
      ∃ valid, ∃ work : pathCost q ≤ Q,
        (⟨.construction q valid,d⟩ : Observation) ∈ (runReal C iv whole).view.observations ∧
        SpongefishCurrentCallerGetter.raw iv (runReal C iv whole).view.observations
          (constructionKey Q iv q work) = some d := by
  dsimp only
  intro q d hit
  obtain ⟨valid,member⟩ := (initialized_recorded C iv _ instanceBytes _ _ calls).1 q d hit
  have present := afterPrefix_replay_included C iv tag instanceBytes prefixProgram calls nonempty _ member
  have cap := observation_cap (real_runs C iv _) _
    (SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes prefixProgram calls A attacker)
    _ present
  refine ⟨valid,cap,present,?_⟩
  rw [SpongefishCurrentCallerGetter.raw_construction iv _ q valid cap]
  have consistent := SpongefishCurrentCallerGetter.real_consistent C iv
    (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram calls)
  rw [SpongefishCurrentCallerGetter.lookup_real C iv _ consistent q valid ⟨_,present,rfl⟩]
  exact congrArg some (consistent _ present).symm

/-- Extract only the actual replay branch from the source operational execution.
Constructor rejection has no branch; replay errors do, and retain their tape. -/
theorem afterPrefix_replay_subrun (iv : Digest32) (tag instanceBytes : List Byte)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (tape : List Call)
    {os : List Observation} {data : SpongefishCurrentInitializedMode.Result}
    (ran : Runs (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram tape)
      os (some data)) :
    ∃ input : SpongefishCurrentInitializedMode.Input, ∃ session result reached,
      eraseResult result = data ∧
      Runs (replayProgram (SpongefishCurrentInitializedMode.initial
        session instanceBytes input.narg input.hints) tape) reached result ∧
      (∀ o ∈ reached, o ∈ os) := by
  obtain ⟨input,attacker,verifier,trace,_,entry⟩ := bind_runs _ _ ran
  obtain ⟨setup,ordinary,replay,entryTrace,_,rest⟩ := bind_runs _ _ entry
  cases setup with
  | none => cases rest
  | some actual =>
    obtain ⟨result,reached,empty,replayTrace,replayed,done⟩ := bind_runs _ _ rest
    cases done
    simp only [List.append_nil] at replayTrace
    subst replay
    refine ⟨input,actual.pending.domain,result,reached,rfl,replayed,?_⟩
    intro o member
    rw [trace,entryTrace]
    exact List.mem_append_right _ (List.mem_append_right _ member)

/-- Cache provenance for the actual initialized operational source, including
the .error byte result. No externally supplied cache invariant is needed. -/
theorem afterPrefix_runs_recorded (iv : Digest32) (tag instanceBytes : List Byte)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (tape : List Call)
    {os : List Observation} {data : SpongefishCurrentInitializedMode.Result}
    (ran : Runs (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram tape)
      os (some data)) :
    ∃ result : Result, eraseResult result = data ∧ Recorded (resultCache result) os := by
  obtain ⟨input,session,result,reached,erased,replayed,included⟩ :=
    afterPrefix_replay_subrun iv tag instanceBytes prefixProgram tape ran
  have recorded := (replay_recorded _ tape [] (empty_recorded []) replayed).1
  exact ⟨result,erased,recorded_mono (by simpa using recorded) included⟩

/-- Actual unchanged Mixed.compile lowering: every cached full digest is backed
both by a public construction observation and its raw draw in the atomic query
trace, with the independent RO answer at the internally bounded key. -/
theorem lowered_cached_provenance (iv : Digest32) (tag instanceBytes : List Byte)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (tape : List Call)
    (A : Nat) (attacker : Counts A prefixProgram)
    (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey (A + SpongefishCurrentInitializedMode.budget tag instanceBytes tape) → Digest32)
    (log : DuplexPublicSimulator.PublicLog) (data : SpongefishCurrentInitializedMode.Result)
    (reached :
      (runIdeal (DuplexPublicSimulator.simulator (A + SpongefishCurrentInitializedMode.budget tag instanceBytes tape))
        ro iv ⟨seed,log⟩ (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram tape)
        _ (Nat.le_refl _) (SpongefishCurrentInitializedMode.afterPrefix_counted
          iv tag instanceBytes prefixProgram tape A attacker)).view.result = some data) :
    let Q := A + SpongefishCurrentInitializedMode.budget tag instanceBytes tape
    let source := SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram tape
    let counted := SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes prefixProgram tape A attacker
    let execution := runIdeal (DuplexPublicSimulator.simulator Q) ro iv ⟨seed,log⟩ source Q (Nat.le_refl Q) counted
    ∃ result : Result, eraseResult result = data ∧
      ∀ q d, resultCache result q = some d →
        ∃ valid, ∃ work : pathCost q ≤ Q,
          (⟨.construction q valid,d⟩ : Observation) ∈ execution.view.observations ∧
          d = ro (constructionKey Q iv q work) ∧
          SpongefishCurrentCallerGetter.raw iv execution.view.observations
            (constructionKey Q iv q work) = some d ∧
          (⟨.inr (constructionKey Q iv q work),d⟩ :
            Sigma (fun _ : PublicCompressionCouplingMixed.Key Q => Digest32)) ∈
            (TypedOracleCompiler.Sampling.execute (PublicCompressionCouplingMixed.oracle seed ro)
              (PublicCompressionCouplingMixed.compile Q iv log source Q (Nat.le_refl Q) counted)).2 := by
  dsimp only
  have ran := ideal_runs
    (DuplexPublicSimulator.simulator (A + SpongefishCurrentInitializedMode.budget tag instanceBytes tape))
    ro iv ⟨seed,log⟩ (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram tape)
    _ (Nat.le_refl _) (SpongefishCurrentInitializedMode.afterPrefix_counted
      iv tag instanceBytes prefixProgram tape A attacker)
  rw [reached] at ran
  obtain ⟨result,erased,recorded⟩ := afterPrefix_runs_recorded iv tag instanceBytes prefixProgram tape ran
  refine ⟨result,erased,?_⟩
  intro q d hit
  obtain ⟨valid,member⟩ := recorded q d hit
  obtain ⟨work,answer,getter⟩ := ideal_observed_getter
    (DuplexPublicSimulator.simulator (A + SpongefishCurrentInitializedMode.budget tag instanceBytes tape))
    ro iv ⟨seed,log⟩ _ _ (Nat.le_refl _) _ q valid d member
  obtain ⟨bound,allocated⟩ := PCSBCSMixedConstructionTrace.ideal_recorded seed ro iv log _ _
    (Nat.le_refl _) _ q valid d member
  exact ⟨valid,work,member,answer,getter,allocated⟩

/-- Completeness for the actual ideal source replay, not a fictitious decoded
tape. `some data` includes every replay rejection; it only excludes constructor
rejection, when no replay branch exists. Source observations alone determine
every getter answer, with no independent oracle fallback. -/
theorem afterPrefix_ideal_replay_complete (iv : Digest32) (tag instanceBytes : List Byte)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (tape : List Call)
    (A : Nat) (attacker : Counts A prefixProgram)
    (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey (A + SpongefishCurrentInitializedMode.budget tag instanceBytes tape) → Digest32)
    (log : DuplexPublicSimulator.PublicLog) (data : SpongefishCurrentInitializedMode.Result)
    (reached :
      (runIdeal (DuplexPublicSimulator.simulator (A + SpongefishCurrentInitializedMode.budget tag instanceBytes tape))
        ro iv ⟨seed,log⟩ (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram tape)
        _ (Nat.le_refl _) (SpongefishCurrentInitializedMode.afterPrefix_counted
          iv tag instanceBytes prefixProgram tape A attacker)).view.result = some data) :
    let Q := A + SpongefishCurrentInitializedMode.budget tag instanceBytes tape
    let source := SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram tape
    let counted := SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes prefixProgram tape A attacker
    let execution := runIdeal (DuplexPublicSimulator.simulator Q) ro iv ⟨seed,log⟩ source Q (Nat.le_refl Q) counted
    ∃ input : SpongefishCurrentInitializedMode.Input, ∃ session result,
      eraseResult result = data ∧
      Recorded (resultCache result) execution.view.observations ∧
      SpongefishCurrentCallerGetter.run
        (SpongefishCurrentCallerGetter.answer (Q := Q) execution.view.observations)
        (replayProgram (SpongefishCurrentInitializedMode.initial session instanceBytes input.narg input.hints) tape) =
          some result := by
  dsimp only
  have ran := ideal_runs
    (DuplexPublicSimulator.simulator (A + SpongefishCurrentInitializedMode.budget tag instanceBytes tape))
    ro iv ⟨seed,log⟩ (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram tape)
    _ (Nat.le_refl _) (SpongefishCurrentInitializedMode.afterPrefix_counted
      iv tag instanceBytes prefixProgram tape A attacker)
  rw [reached] at ran
  obtain ⟨input,session,result,observations,erased,replayed,included⟩ :=
    afterPrefix_replay_subrun iv tag instanceBytes prefixProgram tape ran
  have provenance := replay_recorded _ tape [] (empty_recorded []) replayed
  refine ⟨input,session,result,erased,recorded_mono (by simpa using provenance.1) included,?_⟩
  apply run_observed replayed
  intro o member
  obtain ⟨q,valid,equal⟩ := provenance.2 o member
  obtain ⟨query,d⟩ := o
  dsimp only at equal
  subst query
  have present := included _ member
  obtain ⟨work,_,getter⟩ := ideal_observed_getter
    (DuplexPublicSimulator.simulator (A + SpongefishCurrentInitializedMode.budget tag instanceBytes tape))
    ro iv ⟨seed,log⟩ _ _ (Nat.le_refl _) _ q valid d present
  rw [SpongefishCurrentCallerGetter.raw_construction iv _ q valid work] at getter
  simpa only [SpongefishCurrentCallerGetter.answer,SpongefishCurrentCallerGetter.bounded,
    work,↓reduceIte] using getter

#print axioms request_recorded
#print axioms request_hit
#print axioms collect_recorded
#print axioms replay_recorded
#print axioms initialized_recorded
#print axioms replay_getter_complete
#print axioms afterPrefix_replay_included
#print axioms afterPrefix_getter
#print axioms afterPrefix_cached_getter
#print axioms afterPrefix_runs_recorded
#print axioms lowered_cached_provenance
#print axioms afterPrefix_replay_complete
#print axioms afterPrefix_replay_subrun
#print axioms afterPrefix_ideal_replay_complete
end Whir.SpongefishCurrentCallerGetterCoverage
