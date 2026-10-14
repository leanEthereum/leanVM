import Whir.PCSBCSPublicCallerAnswers
import Whir.PCSBCSSourceCallerOriginal

/-! Public caller completion executes missing literal construction plans through
`Sampling`, retaining every reached primitive observation in chronological order.
Existing answers and duplicate coordinates are replayed without oracle draws.
This is a deterministic reconstruction lemma, not a Fiat--Shamir security theorem
or a conversion to a newest-first, strictly-earlier source log. Integration must
still relate these real mode answers to the finite source table and establish
causality of the generated primitive queries at the selected source boundary. -/
set_option autoImplicit false
namespace Whir.PCSBCSPublicCallerCompletion
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open TypedOracleCompiler PublicCompressionProgram PublicMerkleLog
open PCSBCSPublicCallerAnswers

/-- Instrument an actual primitive computation, without changing its draws. -/
def record {R : Type} {Q : Nat} : Computation R Q → Computation (R × PublicLog) Q
  | .ret r => .ret (r,[])
  | .draw n next => .draw n (fun d =>
      mapResult (fun result => (result.1,(n,d) :: result.2)) (record (next d)))

theorem record_execute {R : Type} (C : PrimitiveOracle) {Q : Nat}
    (p : Computation R Q) :
    Sampling.execute C (record p) =
      (((Sampling.execute C p).1,toLog (Sampling.execute C p).2),
        (Sampling.execute C p).2) := by
  induction p with
  | ret => rfl
  | draw n next ih =>
      simp only [record,Sampling.execute,execute_mapResult,ih,toLog,List.map_cons]

@[simp] theorem record_eval {R : Type} (C : PrimitiveOracle) {Q : Nat}
    (p : Computation R Q) :
    Sampling.eval C (record p) =
      (Sampling.eval C p,toLog (Sampling.execute C p).2) := by
  have h := congrArg Prod.fst (record_execute C p)
  simpa only [Sampling.execute_value] using h

/-- A structural cap computed from the literal requests, never supplied by a caller. -/
@[reducible] def budget : List Coordinate → Nat
  | [] => 0
  | q :: rest => (DuplexEncoding.plan q).length + budget rest

theorem budget_sum (requests : List Coordinate) :
    budget requests = (requests.map pathCost).sum := by
  induction requests with
  | nil => rfl
  | cons q rest ih => simp only [budget,List.map_cons,List.sum_cons,pathCost,ih]

/-- The cache grows only by observations made by the real primitive oracle.
A missing output executes the entire literal plan; it never evaluates a pure C
callback, invents a digest, or accepts an external completion certificate. -/
def complete (iv : Digest32) (log : PublicLog) :
    (requests : List Coordinate) → Computation PublicLog (budget requests)
  | [] => .ret log
  | q :: rest =>
      match answer? log iv q with
      | some _ => Sampling.pad (by simp [budget]) (complete iv log rest)
      | none => Sampling.bind (record (planCalls iv (DuplexEncoding.plan q)))
          (fun observed => complete iv (log ++ observed.2) rest)

/-- The returned log is exactly the old log followed by the actual reached
chronological trace. Padding the cap introduces no physical operation. -/
theorem complete_log (C : PrimitiveOracle) (iv : Digest32) (log : PublicLog)
    (requests : List Coordinate) :
    (Sampling.execute C (complete iv log requests)).1 =
      log ++ toLog (Sampling.execute C (complete iv log requests)).2 := by
  induction requests generalizing log with
  | nil => simp [complete,Sampling.execute,toLog]
  | cons q rest ih =>
      simp only [complete]
      split
      · simpa only [Sampling.execute_pad] using ih log
      · simp only [Sampling.execute_bind,record_eval,record_execute]
        rw [ih]
        simp only [toLog,List.map_append,List.append_assoc]

/-- All generated records are authentic, independently of the initial cache. -/
theorem generated_authentic (C : PrimitiveOracle) (iv : Digest32)
    (log : PublicLog) (requests : List Coordinate) :
    AuthenticLog C (toLog (Sampling.execute C (complete iv log requests)).2) :=
  execute_authentic C _

theorem complete_authentic (C : PrimitiveOracle) (iv : Digest32)
    (log : PublicLog) (auth : AuthenticLog C log) (requests : List Coordinate) :
    AuthenticLog C (Sampling.execute C (complete iv log requests)).1 := by
  rw [complete_log]
  intro n d member
  rcases List.mem_append.mp member with old | fresh
  · exact auth n d old
  · exact generated_authentic C iv log requests n d fresh

theorem complete_preserves (C : PrimitiveOracle) (iv : Digest32)
    (log : PublicLog) (requests : List Coordinate) (event : Node × Digest32)
    (member : event ∈ log) :
    event ∈ (Sampling.execute C (complete iv log requests)).1 := by
  rw [complete_log]
  exact List.mem_append_left _ member

/-- Authentic extension cannot change a successfully replayed public answer. -/
theorem replayFrom_extension (C : PrimitiveOracle) (old new : PublicLog)
    (auth : AuthenticLog C new) (contains : ∀ event ∈ old, event ∈ new)
    (cv : Digest32) (plan : List DuplexEncoding.Instruction) (d : Digest32)
    (accepted : replayFrom old cv plan = some d) :
    replayFrom new cv plan = some d := by
  induction plan generalizing cv with
  | nil => exact accepted
  | cons instruction rest ih =>
      simp only [replayFrom,Option.bind_eq_bind] at accepted
      obtain ⟨value,found,later⟩ := Option.bind_eq_some_iff.mp accepted
      have member := contains _ (lookup_mem found)
      have actual := auth _ _ member
      have present := lookup_authentic_member C new auth member
      rw [actual] at present
      simp only [replayFrom,present,Option.bind_eq_bind,Option.bind_some]
      exact ih value later

theorem answer_extension (C : PrimitiveOracle) (old new : PublicLog)
    (auth : AuthenticLog C new) (contains : ∀ event ∈ old, event ∈ new)
    (iv : Digest32) (q : Coordinate) (d : Digest32)
    (accepted : answer? old iv q = some d) : answer? new iv q = some d :=
  replayFrom_extension C old new auth contains iv _ d accepted

/-- Every requested getter actually succeeds and returns the real mode answer.
There is no hypothesis that an earlier output had already been queried. -/
theorem complete_answers (C : PrimitiveOracle) (iv : Digest32)
    (log : PublicLog) (auth : AuthenticLog C log) (requests : List Coordinate) :
    ∀ q ∈ requests, answer? (Sampling.execute C (complete iv log requests)).1 iv q =
      some (evalCoordinate (compressionOf C) iv q) := by
  induction requests generalizing log with
  | nil => simp
  | cons q rest ih =>
      cases found : answer? log iv q with
      | some d =>
          have actual := answer_sound C log auth iv q d found
          simp only [complete,found,Sampling.execute_pad]
          intro r member
          rcases List.mem_cons.mp member with equal | member
          · subst r
            rw [actual]
            exact answer_extension C log _ (complete_authentic C iv log auth rest)
              (complete_preserves C iv log rest) iv q d found
          · exact ih log auth r member
      | none =>
          let trace := toLog (Sampling.execute C
            (planCalls iv (DuplexEncoding.plan q))).2
          have extendedAuth : AuthenticLog C (log ++ trace) := by
            intro n d member
            rcases List.mem_append.mp member with old | fresh
            · exact auth n d old
            · exact execute_authentic C (planCalls iv (DuplexEncoding.plan q)) n d fresh
          have accepted : answer? (log ++ trace) iv q =
              some (evalCoordinate (compressionOf C) iv q) := by
            apply answer_from_recorded_construction C _ extendedAuth iv q
            exact fun event member => List.mem_append_right _ member
          simp only [complete,found,Sampling.execute_bind,record_eval]
          change ∀ r ∈ q :: rest,
            answer? (Sampling.execute C (complete iv (log ++ trace) rest)).1 iv r =
              some (evalCoordinate (compressionOf C) iv r)
          intro r member
          rcases List.mem_cons.mp member with equal | member
          · subst r
            exact answer_extension C (log ++ trace) _
              (complete_authentic C iv _ extendedAuth rest)
              (complete_preserves C iv (log ++ trace) rest) iv q _ accepted
          · exact ih (log ++ trace) extendedAuth r member

/-- Count actual reached compression draws, not nominal fees. -/
theorem complete_draws_le (C : PrimitiveOracle) (iv : Digest32)
    (log : PublicLog) (requests : List Coordinate) :
    (Sampling.execute C (complete iv log requests)).2.length ≤
      (requests.map pathCost).sum := by
  simpa only [budget_sum] using
    (Sampling.execute_runs C (complete iv log requests)).length_le

/-- Exact operational accounting for a missing head request. -/
theorem missing_draws (C : PrimitiveOracle) (iv : Digest32) (log : PublicLog)
    (q : Coordinate) (rest : List Coordinate) (missing : answer? log iv q = none) :
    (Sampling.execute C (complete iv log (q :: rest))).2.length = pathCost q +
      (Sampling.execute C (complete iv
        (log ++ toLog (Sampling.execute C (planCalls iv (DuplexEncoding.plan q))).2)
        rest)).2.length := by
  simp only [complete,missing,Sampling.execute_bind,record_eval,record_execute,
    List.length_append,planCalls_count,pathCost]

/-- Literal plans have both a seed and a terminal, even for empty histories. -/
theorem pathCost_nonempty (q : Coordinate) : 2 ≤ pathCost q := by
  simp [pathCost,DuplexEncoding.plan]

/-- Absence cannot silently return a placeholder: it reaches at least the
literal seed and terminal draws before proceeding to the remaining requests. -/
theorem missing_has_draws (C : PrimitiveOracle) (iv : Digest32) (log : PublicLog)
    (q : Coordinate) (rest : List Coordinate) (missing : answer? log iv q = none) :
    2 ≤ (Sampling.execute C (complete iv log (q :: rest))).2.length := by
  rw [missing_draws C iv log q rest missing]
  have nonempty := pathCost_nonempty q
  omega

/-- An already observed answer is reused and costs no primitive draw. -/
theorem reuse (C : PrimitiveOracle) (iv : Digest32) (log : PublicLog)
    (q : Coordinate) (d : Digest32) (present : answer? log iv q = some d) :
    Sampling.execute C (complete iv log [q]) = (log,[]) := by
  simp [complete,present,Sampling.execute]

/-- In particular, completing a previously requested duplicate is draw-free. -/
theorem completed_reuse (C : PrimitiveOracle) (iv : Digest32)
    (log : PublicLog) (auth : AuthenticLog C log) (requests : List Coordinate)
    (q : Coordinate) (member : q ∈ requests) :
    Sampling.execute C (complete iv
      (Sampling.execute C (complete iv log requests)).1 [q]) =
        ((Sampling.execute C (complete iv log requests)).1,[]) :=
  reuse C iv _ q _ (complete_answers C iv log auth requests q member)

/-- Entry-level executable completion. No frame-validity or admissibility
assumption is needed for the literal evaluation/replay identity. -/
def callerCompletion (iv : Digest32) (log : PublicLog) (entry : FramedHistory) :
    Computation PublicLog (budget (WHIRCallerOutputs.callerOutputs entry)) :=
  complete iv log (WHIRCallerOutputs.callerOutputs entry)

theorem callerCompletion_answers (C : PrimitiveOracle) (iv : Digest32)
    (log : PublicLog) (auth : AuthenticLog C log) (entry : FramedHistory) :
    ∀ q ∈ WHIRCallerOutputs.callerOutputs entry,
      answer? (Sampling.execute C (callerCompletion iv log entry)).1 iv q =
        some (evalCoordinate (compressionOf C) iv q) :=
  complete_answers C iv log auth _

/-- Successful totality of every requested public getter. -/
theorem callerCompletion_total (C : PrimitiveOracle) (iv : Digest32)
    (log : PublicLog) (auth : AuthenticLog C log) (entry : FramedHistory) :
    ∀ q ∈ WHIRCallerOutputs.callerOutputs entry,
      (answer? (Sampling.execute C (callerCompletion iv log entry)).1 iv q).isSome := by
  intro q member
  rw [callerCompletion_answers C iv log auth entry q member]
  rfl

/-- A total, fallback-free getter on precisely the requested finite domain.
This getter takes only the completed public log, never the primitive oracle.
The proof removes the impossible `none` branch; it supplies no digest. -/
def callerGetter (iv : Digest32) (log : PublicLog) (entry : FramedHistory)
    (available : ∀ q ∈ WHIRCallerOutputs.callerOutputs entry, (answer? log iv q).isSome)
    (q : {q : Coordinate // q ∈ WHIRCallerOutputs.callerOutputs entry}) : Digest32 :=
  (answer? log iv q.val).get (available q.val q.property)

theorem callerGetter_correct (C : PrimitiveOracle) (iv : Digest32)
    (log : PublicLog) (auth : AuthenticLog C log) (entry : FramedHistory)
    (available : ∀ q ∈ WHIRCallerOutputs.callerOutputs entry, (answer? log iv q).isSome)
    (q : {q : Coordinate // q ∈ WHIRCallerOutputs.callerOutputs entry}) :
    callerGetter iv log entry available q = evalCoordinate (compressionOf C) iv q.val :=
  (answer_sound C log auth iv q.val _
    (Option.some_get (available q.val q.property)).symm).symm

local instance : DecidableEq Terminal := by
  intro a b
  cases a <;> cases b <;> simp <;> infer_instance

local instance : DecidableEq Coordinate := by
  intro a b
  cases a
  cases b
  simp only [Coordinate.mk.injEq]
  infer_instance

/-- Executable scanner callback. Every requested coordinate uses the actual
public getter, with no missing-answer fallback. The separate outside callback
is used only for coordinates the caller does not observe, never for absence. -/
def callerAnswers (iv : Digest32) (log : PublicLog) (entry : FramedHistory)
    (available : ∀ q ∈ WHIRCallerOutputs.callerOutputs entry, (answer? log iv q).isSome)
    (outside : Coordinate → Digest32) (q : Coordinate) : Digest32 :=
  if member : q ∈ WHIRCallerOutputs.callerOutputs entry then
    callerGetter iv log entry available ⟨q,member⟩
  else outside q

theorem callerAnswers_on (iv : Digest32) (log : PublicLog) (entry : FramedHistory)
    (available : ∀ q ∈ WHIRCallerOutputs.callerOutputs entry, (answer? log iv q).isSome)
    (outside : Coordinate → Digest32) (q : Coordinate)
    (member : q ∈ WHIRCallerOutputs.callerOutputs entry) :
    callerAnswers iv log entry available outside q =
      callerGetter iv log entry available ⟨q,member⟩ := by
  simp only [callerAnswers,dite_eq_left member]


/-- The scanner may use any total extension of the actual finite getter. Its
values outside callerOutputs are irrelevant, including for parser failures. -/
theorem original_completed (C : PrimitiveOracle) (iv : Digest32)
    (log : PublicLog) (auth : AuthenticLog C log) (entry : FramedHistory)
    (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (answers : Coordinate → Digest32)
    (extendsGetter : ∀ q (member : q ∈ WHIRCallerOutputs.callerOutputs entry),
      answers q = callerGetter iv (Sampling.execute C (callerCompletion iv log entry)).1
        entry (callerCompletion_total C iv log auth entry) ⟨q,member⟩) :
    PCSBCSSourceCallerOriginal.original p layout saved entry answers =
      PCSBCSSourceCallerOriginal.original p layout saved entry
        (evalCoordinate (compressionOf C) iv) := by
  apply PCSBCSSourceCallerOriginal.original_prior_only
  intro q member
  rw [extendsGetter q member]
  exact callerGetter_correct C iv _ (complete_authentic C iv log auth _)
    entry _ ⟨q,member⟩

/-- End-to-end original caller equality for the concrete public callback:
no extensional-answer premise or supplied completion digest is required. -/
theorem original_resolved (C : PrimitiveOracle) (iv : Digest32)
    (log : PublicLog) (auth : AuthenticLog C log) (entry : FramedHistory)
    (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (outside : Coordinate → Digest32) :
    PCSBCSSourceCallerOriginal.original p layout saved entry
      (callerAnswers iv (Sampling.execute C (callerCompletion iv log entry)).1
        entry (callerCompletion_total C iv log auth entry) outside) =
      PCSBCSSourceCallerOriginal.original p layout saved entry
        (evalCoordinate (compressionOf C) iv) := by
  apply original_completed C iv log auth entry p layout saved
  intro q member
  exact callerAnswers_on iv _ entry _ outside q member


#print axioms complete_log
#print axioms complete_authentic
#print axioms complete_answers
#print axioms complete_draws_le
#print axioms missing_draws
#print axioms missing_has_draws
#print axioms completed_reuse
#print axioms callerGetter_correct
#print axioms original_completed
#print axioms original_resolved
end Whir.PCSBCSPublicCallerCompletion
