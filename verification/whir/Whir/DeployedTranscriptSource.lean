import Whir.DeployedTranscriptGame

/-! HISTORICAL pre-#552 source-function refinement, not the current merged mode.
The reference interpreter calls the hand-ported historical operations rather
than compression programs; all public observations and contexts are retained. -/
namespace Whir.DeployedTranscriptGame
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicCompressionProgram TypedOracleCompiler DeployedTranscript
open DeployedTranscriptCoupling (ChallengeOracle TailOracle publicOracle)

def Entry.evaluate (C : PrimitiveOracle) : Entry → Context
  | .seeded iv publicInput => new C iv publicInput
  | .label bytes => fromLabel C bytes

theorem Entry.calls_source (C : PrimitiveOracle) (entry : Entry) :
    (CompressionProgram.run C entry.calls).1 = entry.evaluate C := by
  cases entry <;> simp only [Entry.calls,Entry.evaluate,CompressionProgram.lower_eval,
    newCalls_eval,fromLabelCalls_eval]

def Operation.evaluate (C : PrimitiveOracle) (context : Context) :
    (operation : Operation) → Context × operation.Answer
  | .observe scalar => (DeployedTranscript.observe C context scalar,())
  | .sample => DeployedTranscript.sample C context
  | .context => (context,context)
  | .state => (context,exportedState C context)
  | .powBase => (context,DeployedTranscript.powBase C context)
  | .absorbNonce nonce => (DeployedTranscript.absorbNonce C context nonce,())

theorem Operation.calls_source (C : PrimitiveOracle) (context : Context)
    (operation : Operation) :
    (CompressionProgram.run C (operation.calls context)).1 = operation.evaluate C context := by
  cases operation with
  | observe scalar =>
    simp only [Operation.calls,Operation.evaluate,CompressionProgram.run_map]
    exact congrArg (fun c : Context => (c,()))
      ((CompressionProgram.lower_eval C _).trans (observeCalls_eval C context scalar))
  | sample =>
    exact (CompressionProgram.lower_eval C _).trans (sampleCalls_eval C context)
  | context => rfl
  | state =>
    simp only [Operation.calls,Operation.evaluate,CompressionProgram.run_map]
    exact congrArg (fun d : Digest32 => (context,d))
      ((CompressionProgram.lower_eval C _).trans (stateCalls_eval C context))
  | powBase =>
    simp only [Operation.calls,Operation.evaluate,CompressionProgram.run_map]
    exact congrArg (fun d : Digest32 => (context,d))
      ((CompressionProgram.lower_eval C _).trans (powBaseCalls_eval C context))
  | absorbNonce nonce =>
    simp only [Operation.calls,Operation.evaluate,CompressionProgram.run_map]
    exact congrArg (fun c : Context => (c,()))
      ((CompressionProgram.lower_eval C _).trans (absorbNonceCalls_eval C context nonce))

def Action.evaluate {k : Nat} (C : PrimitiveOracle) (heap : Heap k) :
    (action : Action k) → Heap k × action.Answer
  | .primitive _ input => (heap,C input)
  | .call handle operation =>
      let result := operation.evaluate C (heap handle)
      (Function.update heap handle result.1,result.2)
  | .clone source destination => (Function.update heap destination (heap source),())
  | .initialize destination entry =>
      (Function.update heap destination (entry.evaluate C),())

theorem Action.calls_source {k : Nat} (C : PrimitiveOracle) (heap : Heap k)
    (action : Action k) :
    (CompressionProgram.run C (action.calls heap)).1 = action.evaluate C heap := by
  cases action <;> simp only [Action.calls,Action.evaluate,
    CompressionProgram.run_map,Operation.calls_source,Entry.calls_source]
  all_goals rfl

def runSource {k : Nat} {R : Type} (C : PrimitiveOracle) (heap : Heap k) :
    Program k R → View k R
  | .done r => ⟨[],r⟩
  | .ask action next =>
      let result := action.evaluate C heap
      prepend action result.2 (runSource C result.1 (next result.2))

theorem compile_source {k : Nat} {R : Type} (C : PrimitiveOracle) (heap : Heap k)
    (program : Program k R) :
    (CompressionProgram.run C (compile heap program)).1 = runSource C heap program := by
  induction program generalizing heap with
  | done => rfl
  | ask action next ih =>
    simp only [compile,CompressionProgram.run_bind,CompressionProgram.run_map,
      Action.calls_source,runSource]
    exact congrArg (prepend action (action.evaluate C heap).2)
      (ih (action.evaluate C heap).2 (action.evaluate C heap).1)

def sourceHeap {k : Nat} (C : PrimitiveOracle) (entries : Fin k → Entry) : Heap k :=
  fun i => (entries i).evaluate C

theorem initializeHeap_source {k : Nat} (C : PrimitiveOracle) (entries : Fin k → Entry) :
    (CompressionProgram.run C (initializeHeap entries)).1 = sourceHeap C entries := by
  induction k with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
    simp only [initializeHeap,CompressionProgram.run_bind,CompressionProgram.run_map,
      Entry.calls_source]
    rw [ih]
    funext i
    cases i using Fin.cases <;> rfl

def sourceExperiment {k : Nat} {R : Type} (C : PrimitiveOracle) (entries : Fin k → Entry)
    (program : Program k R) : View k R := runSource C (sourceHeap C entries) program

theorem experiment_source {k : Nat} {R : Type} (C : PrimitiveOracle) (entries : Fin k → Entry)
    (program : Program k R) :
    (CompressionProgram.run C (experiment entries program)).1 = sourceExperiment C entries program := by
  simp only [experiment,CompressionProgram.run_bind,initializeHeap_source,
    compile_source,sourceExperiment]

/-- Actual source interpreter in both finite games, with all source entry and
public-view conventions preserved. No full-message RO independence is claimed. -/
theorem deployed_source_coupling {k : Nat} {R : Type} (entries : Fin k → Entry)
    (program : Program k R) (D : View k R → Bool) :
    distinguishProbability (fun C : PrimitiveOracle => sourceExperiment C entries program) D =
      distinguishProbability (fun coins : ChallengeOracle × TailOracle =>
        sourceExperiment (publicOracle coins.1 coins.2) entries program) D := by
  rw [distinguish_average (inferInstance : Fintype PrimitiveOracle),
    distinguish_average (inferInstance : Fintype (ChallengeOracle × TailOracle))]
  exact DeployedTranscriptCoupling.public_table_expectation _

#print axioms compile_source
#print axioms experiment_source
#print axioms deployed_source_coupling
end Whir.DeployedTranscriptGame
