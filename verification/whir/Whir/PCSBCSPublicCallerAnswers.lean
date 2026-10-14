import Whir.PublicCompressionProgram

/-! Caller challenge answers recovered only from a supplied earlier physical
compression log. No private primitive oracle, future log, or output-table getter
is evaluated by the decoder. Completeness is proved for literal construction
traces; relating such a trace to a particular source boundary remains explicit. -/
set_option autoImplicit false
namespace Whir.PCSBCSPublicCallerAnswers
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open TypedOracleCompiler PublicCompressionProgram PublicMerkleLog

/-- Replay one exact duplex plan using public cache lookups. Absence rejects. -/
def replayFrom (log : PublicLog) (cv : Digest32) :
    List DuplexEncoding.Instruction → Option Digest32
  | [] => some cv
  | instruction :: rest => do
      let answer ← PublicMerkleLog.lookup log ⟨cv,instruction.1,instruction.2,true⟩
      replayFrom log answer rest

/-- The complete source coordinate determines its literal tagged input plan. -/
def answer? (log : PublicLog) (iv : Digest32) (coordinate : Coordinate) : Option Digest32 :=
  replayFrom log iv (DuplexEncoding.plan coordinate)

/-- Total scanner callbacks can use an inert default on a missing caller query.
This default is not authenticated or asserted to be a real caller answer. -/
def answer (log : PublicLog) (iv : Digest32) (coordinate : Coordinate) : Digest32 :=
  (answer? log iv coordinate).getD (fun _ => 0)

theorem replayFrom_sound (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (cv : Digest32) (plan : List DuplexEncoding.Instruction)
    (result : Digest32) (accepted : replayFrom log cv plan = some result) :
    evalPlan (compressionOf C) cv plan = result := by
  induction plan generalizing cv with
  | nil => simpa only [replayFrom,Option.some.injEq,evalPlan,List.foldl_nil] using accepted
  | cons instruction rest ih =>
      simp only [replayFrom,Option.bind_eq_bind] at accepted
      obtain ⟨value,found,next⟩ := Option.bind_eq_some_iff.mp accepted
      have actual := auth _ _ (lookup_mem found)
      change evalPlan (compressionOf C) (C ⟨cv,instruction.1,instruction.2,true⟩) rest = result
      rw [actual]
      exact ih value next

theorem answer_sound (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (iv : Digest32) (coordinate : Coordinate)
    (result : Digest32) (accepted : answer? log iv coordinate = some result) :
    evalCoordinate (compressionOf C) iv coordinate = result := by
  rw [← plan_evaluate]
  exact replayFrom_sound C log auth iv _ result accepted

/-- Every recorded plan node suffices, regardless of cache order or duplicates. -/
theorem replayFrom_complete (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (cv : Digest32) (plan : List DuplexEncoding.Instruction)
    (present : ∀ event ∈ toLog (Sampling.execute C (planCalls cv plan)).2, event ∈ log) :
    replayFrom log cv plan = some (evalPlan (compressionOf C) cv plan) := by
  induction plan generalizing cv with
  | nil => rfl
  | cons instruction rest ih =>
      have head := present (⟨cv,instruction.1,instruction.2,true⟩,
        C ⟨cv,instruction.1,instruction.2,true⟩) (by simp [planCalls,Sampling.execute,toLog])
      have found := lookup_authentic_member C log auth head
      simp only [replayFrom,found,Option.bind_eq_bind,Option.bind_some]
      change replayFrom log (C ⟨cv,instruction.1,instruction.2,true⟩) rest =
        some (evalPlan (compressionOf C) (C ⟨cv,instruction.1,instruction.2,true⟩) rest)
      apply ih
      intro event member
      apply present event
      simp only [planCalls,Sampling.execute,toLog,List.map_cons,List.mem_cons]
      exact Or.inr member

/-- A literal earlier complete construction trace yields its actual caller coin.
The decoder takes only that log, not the primitive oracle used in this theorem. -/
theorem answer_from_recorded_construction (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (iv : Digest32) (coordinate : Coordinate)
    (present : ∀ event ∈ toLog (Sampling.execute C
      (planCalls iv (DuplexEncoding.plan coordinate))).2, event ∈ log) :
    answer? log iv coordinate = some (evalCoordinate (compressionOf C) iv coordinate) := by
  unfold answer?
  rw [replayFrom_complete C log auth iv _ present,plan_evaluate]

theorem answer_from_literal_trace (C : PrimitiveOracle) (iv : Digest32)
    (coordinate : Coordinate) :
    answer? (toLog (Sampling.execute C (planCalls iv (DuplexEncoding.plan coordinate))).2)
      iv coordinate = some (evalCoordinate (compressionOf C) iv coordinate) := by
  apply answer_from_recorded_construction C _ (execute_authentic C _) iv coordinate
  exact fun _ member => member

#print axioms replayFrom_sound
#print axioms answer_sound
#print axioms replayFrom_complete
#print axioms answer_from_recorded_construction
#print axioms answer_from_literal_trace
end Whir.PCSBCSPublicCallerAnswers
