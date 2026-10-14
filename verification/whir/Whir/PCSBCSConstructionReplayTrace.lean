import Whir.PCSBCSPublicCallerAnswers

/-! Physical replay for the actual public-compression compiler. `queryTrace`,
`primitiveLog`, and the prefixes in `AskBoundary` are chronological execute
traces. A boundary prefix includes the current query's complete physical plan;
it is not a strictly-prior-query log. Newest-first histories are obtained only
by the explicit reversal lemmas below. No availability or security hypothesis
is used: plan membership is derived from compilation along the real run. -/
set_option autoImplicit false
namespace Whir.PCSBCSConstructionReplayTrace
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open TypedOracleCompiler PublicCompressionProgram PublicMerkleLog

/-- Actual Sampling calls of one query, in chronological order. -/
def queryTrace (C : PrimitiveOracle) (iv : Digest32) (q : Query) : PublicLog :=
  toLog (Sampling.execute C (queryCalls iv q)).2

theorem queryTrace_authentic (C : PrimitiveOracle) (iv : Digest32) (q : Query) :
    AuthenticLog C (queryTrace C iv q) := execute_authentic C _

/-- The compiler emits this query's calls before its actual adaptive continuation. -/
theorem primitiveLog_ask {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (q : Query) (next : Digest32 → Program R) (Q : Nat)
    (counted : Counts Q (.ask q next)) :
    primitiveLog C iv (.ask q next) Q counted = queryTrace C iv q ++
      primitiveLog C iv (next (realAnswer C iv q)) (Q-q.cost) (counted.2 _) := by
  simp only [primitiveLog,PublicCompressionProgram.compile,Sampling.execute_pad,
    Sampling.execute_bind,execute_mapResult,queryCalls_eval,toLog,List.map_append,queryTrace]

/-- Each public observation has its real answer, without an assumed soundness contract. -/
theorem observation_answer {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (o : Observation)
    (observed : o ∈ (runReal C iv p).view.observations) :
    o.answer = realAnswer C iv o.query := by
  induction p with
  | done => simp [runReal] at observed
  | ask q next ih =>
    simp only [runReal,prepend,List.mem_cons] at observed
    rcases observed with rfl | observed
    · rfl
    · exact ih _ observed

/-- Actual compile recursion supplies every physical call of every observed query. -/
theorem observation_trace_membership {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (Q : Nat) (counted : Counts Q p) (o : Observation)
    (observed : o ∈ (runReal C iv p).view.observations) :
    ∀ event ∈ queryTrace C iv o.query, event ∈ primitiveLog C iv p Q counted := by
  induction p generalizing Q with
  | done => simp [runReal] at observed
  | ask q next ih =>
    rw [primitiveLog_ask]
    simp only [runReal,prepend,List.mem_cons] at observed
    rcases observed with rfl | observed
    · exact fun _ member => List.mem_append_left _ member
    · intro event member
      exact List.mem_append_right _ (ih _ _ (counted.2 _) observed event member)

/-- Literal plan membership is a consequence of compilation, not an input contract. -/
theorem construction_plan_membership {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (Q : Nat) (counted : Counts Q p)
    (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate) (d : Digest32)
    (observed : (⟨.construction coordinate valid,d⟩ : Observation) ∈
      (runReal C iv p).view.observations) :
    ∀ event ∈ toLog (Sampling.execute C (planCalls iv (DuplexEncoding.plan coordinate))).2,
      event ∈ primitiveLog C iv p Q counted :=
  observation_trace_membership C iv p Q counted _ observed

/-- Every construction observation is recovered from the compiler's full physical log. -/
theorem construction_replay {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (Q : Nat) (counted : Counts Q p)
    (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate) (d : Digest32)
    (observed : (⟨.construction coordinate valid,d⟩ : Observation) ∈
      (runReal C iv p).view.observations) :
    PCSBCSPublicCallerAnswers.answer? (primitiveLog C iv p Q counted) iv coordinate = some d := by
  have actual := observation_answer C iv p _ observed
  change d = evalCoordinate (compressionOf C) iv coordinate at actual
  rw [actual]
  exact PCSBCSPublicCallerAnswers.answer_from_recorded_construction C _
    (primitiveLog_authentic C iv p Q counted) iv coordinate
    (construction_plan_membership C iv p Q counted coordinate valid d observed)

/-- A reached ask boundary of the real adaptive run. `before` contains only the
physical calls of earlier asks, chronologically; no future continuation is run
in constructing it. The current query's own calls are added for replay. -/
inductive AskBoundary (C : PrimitiveOracle) (iv : Digest32) {R : Type} :
    Program R → PublicLog → Query → (Digest32 → Program R) → Prop where
  | here (q : Query) (next : Digest32 → Program R) :
      AskBoundary C iv (.ask q next) [] q next
  | step (head : Query) (tail : Digest32 → Program R)
      {before : PublicLog} {q : Query} {next : Digest32 → Program R}
      (reached : AskBoundary C iv (tail (realAnswer C iv head)) before q next) :
      AskBoundary C iv (.ask head tail) (queryTrace C iv head ++ before) q next

/-- Every actual observation has a reached boundary, including repeated queries. -/
theorem observation_boundary {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (o : Observation)
    (observed : o ∈ (runReal C iv p).view.observations) :
    ∃ before next, AskBoundary C iv p before o.query next ∧
      o.answer = realAnswer C iv o.query := by
  induction p with
  | done => simp [runReal] at observed
  | ask q tail ih =>
    simp only [runReal,prepend,List.mem_cons] at observed
    rcases observed with rfl | observed
    · exact ⟨[],tail,.here q tail,rfl⟩
    · obtain ⟨before,next,reached,actual⟩ := ih _ observed
      exact ⟨queryTrace C iv q ++ before,next,.step q tail reached,actual⟩

/-- The reached boundary gives an exact chronological split of the actual
compiled trace, with a Counts-certified actual remainder. -/
theorem boundary_physical_split {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    {p : Program R} {before : PublicLog} {q : Query} {next : Digest32 → Program R}
    (reached : AskBoundary C iv p before q next) (Q : Nat) (counted : Counts Q p) :
    ∃ (remaining : Nat) (restCounted : Counts remaining (next (realAnswer C iv q))),
      primitiveLog C iv p Q counted = (before ++ queryTrace C iv q) ++
        primitiveLog C iv (next (realAnswer C iv q)) remaining restCounted := by
  induction reached generalizing Q with
  | here q next =>
    refine ⟨Q-q.cost,counted.2 _,?_⟩
    simpa only [List.nil_append] using (primitiveLog_ask C iv q next Q counted)
  | step head tail reached ih =>
    obtain ⟨remaining,restCounted,split⟩ := ih (Q-head.cost) (counted.2 _)
    refine ⟨remaining,restCounted,?_⟩
    rw [primitiveLog_ask,split]
    simp only [List.append_assoc]

/-- Earlier physical calls are authenticated by execute recursion alone. -/
theorem boundary_before_authentic {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    {p : Program R} {before : PublicLog} {q : Query} {next : Digest32 → Program R}
    (reached : AskBoundary C iv p before q next) : AuthenticLog C before := by
  induction reached with
  | here => intro n d member; cases member
  | step head tail reached ih =>
    intro n d member
    rcases List.mem_append.mp member with member | member
    · exact queryTrace_authentic C iv head n d member
    · exact ih n d member

/-- Replay uses only earlier calls and the current query's own plan. Neither
Counts, the remainder, nor any future answers are needed by this theorem. -/
theorem boundary_prefix_replay {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    {p : Program R} {before : PublicLog} {coordinate : Coordinate}
    {valid : DuplexEncoding.Admissible coordinate} {next : Digest32 → Program R}
    (reached : AskBoundary C iv p before (.construction coordinate valid) next) :
    PCSBCSPublicCallerAnswers.answer?
      (before ++ queryTrace C iv (.construction coordinate valid)) iv coordinate =
      some (evalCoordinate (compressionOf C) iv coordinate) := by
  apply PCSBCSPublicCallerAnswers.answer_from_recorded_construction C
  · intro n d member
    rcases List.mem_append.mp member with member | member
    · exact boundary_before_authentic C iv reached n d member
    · exact queryTrace_authentic C iv _ n d member
  · exact fun _ member => List.mem_append_right _ member

/-- Explicit conversion: chronological membership is unchanged by reversal. -/
theorem reverse_membership (log : PublicLog) (event : Node × Digest32) :
    event ∈ log.reverse ↔ event ∈ log := List.mem_reverse

/-- Reversal converts the full chronological split to a newest-first split.
The future is the left segment, and is excluded from the boundary history. -/
theorem boundary_newest_first_split {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    {p : Program R} {before : PublicLog} {q : Query} {next : Digest32 → Program R}
    (reached : AskBoundary C iv p before q next) (Q : Nat) (counted : Counts Q p) :
    ∃ (remaining : Nat) (restCounted : Counts remaining (next (realAnswer C iv q))),
      (primitiveLog C iv p Q counted).reverse =
        (primitiveLog C iv (next (realAnswer C iv q)) remaining restCounted).reverse ++
          (queryTrace C iv q).reverse ++ before.reverse := by
  obtain ⟨remaining,restCounted,split⟩ := boundary_physical_split C iv reached Q counted
  refine ⟨remaining,restCounted,?_⟩
  rw [split]
  simp only [List.reverse_append,List.append_assoc]

/-- Actual boundary replay also succeeds in newest-first scanner order. This
is a proved reversal conversion, not a chronological/strictly-earlier conflation. -/
theorem boundary_newest_first_replay {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    {p : Program R} {before : PublicLog} {coordinate : Coordinate}
    {valid : DuplexEncoding.Admissible coordinate} {next : Digest32 → Program R}
    (reached : AskBoundary C iv p before (.construction coordinate valid) next) :
    PCSBCSPublicCallerAnswers.answer?
      (before ++ queryTrace C iv (.construction coordinate valid)).reverse iv coordinate =
      some (evalCoordinate (compressionOf C) iv coordinate) := by
  apply PCSBCSPublicCallerAnswers.answer_from_recorded_construction C
  · intro n d member
    rcases List.mem_append.mp (List.mem_reverse.mp member) with member | member
    · exact boundary_before_authentic C iv reached n d member
    · exact queryTrace_authentic C iv _ n d member
  · intro event member
    exact List.mem_reverse.mpr (List.mem_append_right _ member)

#print axioms construction_plan_membership
#print axioms construction_replay
#print axioms observation_boundary
#print axioms boundary_physical_split
#print axioms boundary_prefix_replay
#print axioms boundary_newest_first_split
#print axioms boundary_newest_first_replay
end Whir.PCSBCSConstructionReplayTrace
