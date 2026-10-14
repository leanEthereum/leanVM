import Whir.DeployedTranscriptCoupling

/-! HISTORICAL pre-#552 tagged-scalar source game, not the current merged mode.
Contexts are created only through the two historical source constructors or
copied from live contexts. Readonly snapshots do not permit injection. The full
public view retains scalars, 256-bit states, chosen-CV calls, and contexts.
The ideal experiment is context-key RO, NOT full-message RO or current DMV. -/
namespace Whir.DeployedTranscriptGame
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicCompressionProgram TypedOracleCompiler DeployedTranscript
open DeployedTranscriptCoupling (ChallengeOracle TailOracle publicOracle)

inductive CompressionProgram (R : Type) where
  | done (result : R)
  | ask (input : Node) (next : Digest32 → CompressionProgram R)

namespace CompressionProgram
variable {R S : Type}

def bind : CompressionProgram R → (R → CompressionProgram S) → CompressionProgram S
  | .done r, next => next r
  | .ask input continuation, next => .ask input (fun d => bind (continuation d) next)

def map (f : R → S) : CompressionProgram R → CompressionProgram S
  | .done r => .done (f r)
  | .ask input next => .ask input (fun d => map f (next d))

def run (C : PrimitiveOracle) : CompressionProgram R → R × Nat
  | .done r => (r,0)
  | .ask input next =>
      let rest := run C (next (C input))
      (rest.1,rest.2+1)

@[simp] theorem run_bind (C : PrimitiveOracle) (p : CompressionProgram R)
    (next : R → CompressionProgram S) :
    run C (bind p next) =
      ((run C (next (run C p).1)).1,(run C p).2+(run C (next (run C p).1)).2) := by
  induction p with
  | done => simp [bind,run]
  | ask input continuation ih => simp [bind,run,ih,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

@[simp] theorem run_map (C : PrimitiveOracle) (f : R → S) (p : CompressionProgram R) :
    run C (map f p) = (f (run C p).1,(run C p).2) := by
  induction p with
  | done => rfl
  | ask input next ih => simp [map,run,ih]

/-- This is a worst-case reply-by-reply resource certificate, not acceptance
conditioning. Source internals and repeated inputs each pay their full calls. -/
def Counts : Nat → CompressionProgram R → Prop
  | _, .done _ => True
  | Q, .ask _ next => 1 ≤ Q ∧ ∀ d, Counts (Q-1) (next d)

theorem run_counted (C : PrimitiveOracle) (p : CompressionProgram R) (Q : Nat)
    (counted : Counts Q p) : (run C p).2 ≤ Q := by
  induction p generalizing Q with
  | done => simp [run]
  | ask input next ih =>
    have ht := ih (C input) (Q-1) (counted.2 _)
    simp only [run]
    have hc := counted.1
    omega

def lower {Q : Nat} : Computation R Q → CompressionProgram R
  | .ret r => .done r
  | .draw input next => .ask input (fun d => lower (next d))

theorem lower_eval {Q : Nat} (C : PrimitiveOracle) (p : Computation R Q) :
    (run C (lower p)).1 = Sampling.eval C p := by
  induction p with
  | ret => rfl
  | draw input next ih => exact ih (C input)

theorem lower_counted {Q : Nat} (p : Computation R Q) : Counts Q (lower p) := by
  induction p with
  | ret => trivial
  | @draw n input next ih => exact ⟨by omega,by simpa using ih⟩

/-- Explicit finite stopping, useful for direct application of finite sampling
lemmas. A counted complete execution never uses the `none` exhaustion branch. -/
def stop : (Q : Nat) → CompressionProgram R → Computation (Option R) Q
  | _, .done r => .ret (some r)
  | 0, .ask _ _ => .ret none
  | Q+1, .ask input next => .draw input (fun d => stop Q (next d))

theorem stop_exact (C : PrimitiveOracle) (p : CompressionProgram R) (Q : Nat)
    (counted : Counts Q p) : Sampling.eval C (stop Q p) = some (run C p).1 := by
  induction p generalizing Q with
  | done => cases Q <;> rfl
  | ask input next ih =>
    cases Q with
    | zero => simp [Counts] at counted
    | succ Q =>
      simp only [Counts,Nat.add_sub_cancel] at counted
      have ht := ih (C input) Q (counted.2 (C input))
      simpa only [stop,Sampling.eval,run] using ht
end CompressionProgram

inductive Entry where
  | seeded (iv publicInput : Digest32)
  | label (bytes : List Byte)

def Entry.calls : Entry → CompressionProgram Context
  | .seeded iv publicInput => CompressionProgram.lower (newCalls iv publicInput)
  | .label bytes => CompressionProgram.lower (fromLabelCalls bytes)

def Entry.cost : Entry → Nat
  | .seeded _ _ => 1
  | .label bytes => (PublicMerkleLog.chunks bytes).length

theorem Entry.counted (entry : Entry) : CompressionProgram.Counts entry.cost entry.calls := by
  cases entry <;> exact CompressionProgram.lower_counted _

inductive Operation where
  | observe (scalar : Scalar24)
  | sample
  | context
  | state
  | powBase
  | absorbNonce (nonce : Scalar24)

def Operation.Answer : Operation → Type
  | .observe _ | .absorbNonce _ => Unit
  | .sample => Scalar24
  | .context => Context
  | .state | .powBase => Digest32

def Operation.cost (context : Context) : Operation → Nat
  | .observe _ => observeCost context
  | .sample => 1
  | .context => 0
  | .state => stateCost context
  | .powBase | .absorbNonce _ => stateCost context+1

/-- Only the source operation's real public answer reaches the continuation.
Internal observe/flush answers remain private; the context operation is readonly. -/
def Operation.calls (context : Context) : (operation : Operation) →
    CompressionProgram (Context × operation.Answer)
  | .observe scalar => CompressionProgram.map (fun c => (c,()))
      (CompressionProgram.lower (observeCalls context scalar))
  | .sample => CompressionProgram.lower (sampleCalls context)
  | .context => .done (context,context)
  | .state => CompressionProgram.map (fun d => (context,d))
      (CompressionProgram.lower (stateCalls context))
  | .powBase => CompressionProgram.map (fun d => (context,d))
      (CompressionProgram.lower (powBaseCalls context))
  | .absorbNonce nonce => CompressionProgram.map (fun c => (c,()))
      (CompressionProgram.lower (absorbNonceCalls context nonce))

theorem CompressionProgram.map_counted {R S : Type} (f : R → S)
    (p : CompressionProgram R) (Q : Nat) (counted : CompressionProgram.Counts Q p) :
    CompressionProgram.Counts Q (CompressionProgram.map f p) := by
  induction p generalizing Q with
  | done => trivial
  | ask input next ih => exact ⟨counted.1,fun d => ih d _ (counted.2 d)⟩

theorem Operation.counted (context : Context) (operation : Operation) :
    CompressionProgram.Counts (operation.cost context) (operation.calls context) := by
  cases operation <;> simp only [Operation.calls,Operation.cost]
  all_goals first
    | exact CompressionProgram.map_counted _ _ _ (CompressionProgram.lower_counted _)
    | exact CompressionProgram.lower_counted _
    | trivial

abbrev Heap (k : Nat) := Fin k → Context

inductive Action (k : Nat) where
  | primitive (purpose : Purpose) (input : Node)
  | call (handle : Fin k) (operation : Operation)
  | clone (source destination : Fin k)
  | initialize (destination : Fin k) (entry : Entry)

def Action.Answer {k : Nat} : Action k → Type
  | .primitive _ _ => Digest32
  | .call _ operation => operation.Answer
  | .clone _ _ | .initialize _ _ => Unit

def Action.calls {k : Nat} (heap : Heap k) : (action : Action k) →
    CompressionProgram (Heap k × action.Answer)
  | .primitive _ input => .ask input (fun d => .done (heap,d))
  | .call handle operation => CompressionProgram.map
      (fun result => (Function.update heap handle result.1,result.2))
      (operation.calls (heap handle))
  | .clone source destination => .done (Function.update heap destination (heap source),())
  | .initialize destination entry => CompressionProgram.map
      (fun context => (Function.update heap destination context,())) entry.calls

inductive Program (k : Nat) (R : Type) where
  | done (result : R)
  | ask (action : Action k) (next : action.Answer → Program k R)

abbrev Observation (k : Nat) := Sigma (fun action : Action k => action.Answer)

structure View (k : Nat) (R : Type) where
  observations : List (Observation k)
  result : R

def prepend {k : Nat} {R : Type} (action : Action k) (answer : action.Answer)
    (view : View k R) : View k R := ⟨⟨action,answer⟩::view.observations,view.result⟩

def compile {k : Nat} {R : Type} (heap : Heap k) : Program k R → CompressionProgram (View k R)
  | .done r => .done ⟨[],r⟩
  | .ask action next => CompressionProgram.bind (action.calls heap) (fun result =>
      CompressionProgram.map (prepend action result.2) (compile result.1 (next result.2)))

/-- Initial contexts also pay their actual constructor calls. No arbitrary
live CV is supplied to the experiment, and clone copies only a live source state. -/
def initializeHeap : {k : Nat} → (Fin k → Entry) → CompressionProgram (Heap k)
  | 0, _ => .done (fun i => Fin.elim0 i)
  | k+1, entries => CompressionProgram.bind (entries 0).calls (fun context =>
      CompressionProgram.map (Fin.cases context)
        (initializeHeap (fun i : Fin k => entries i.succ)))

def experiment {k : Nat} {R : Type} (entries : Fin k → Entry) (program : Program k R) :
    CompressionProgram (View k R) :=
  CompressionProgram.bind (initializeHeap entries) (fun heap => compile heap program)

noncomputable def realProbability {k : Nat} {R : Type} (entries : Fin k → Entry)
    (program : Program k R) (D : View k R → Bool) : ℚ :=
  distinguishProbability (fun C : PrimitiveOracle => (CompressionProgram.run C
    (experiment entries program)).1) D

noncomputable def idealProbability {k : Nat} {R : Type} (entries : Fin k → Entry)
    (program : Program k R) (D : View k R → Bool) : ℚ :=
  distinguishProbability (fun coins : ChallengeOracle × TailOracle =>
    (CompressionProgram.run (publicOracle coins.1 coins.2) (experiment entries program)).1) D

/-- End-to-end full-view equality for all adaptive deployed operations, both
actual constructors, readonly contexts, clones, and shared public primitives.
This endpoint is the explicitly defined context-key experiment only. -/
theorem actual_source_context_game_coupling {k : Nat} {R : Type}
    (entries : Fin k → Entry) (program : Program k R) (D : View k R → Bool) :
    realProbability entries program D = idealProbability entries program D := by
  unfold realProbability idealProbability
  rw [distinguish_average (inferInstance : Fintype PrimitiveOracle),
    distinguish_average (inferInstance : Fintype (ChallengeOracle × TailOracle))]
  exact DeployedTranscriptCoupling.public_table_expectation _

#print axioms Entry.counted
#print axioms Operation.counted
#print axioms CompressionProgram.stop_exact
#print axioms actual_source_context_game_coupling
end Whir.DeployedTranscriptGame
