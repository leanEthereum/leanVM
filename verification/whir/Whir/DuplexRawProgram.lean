import Whir.DuplexModeGame
import Whir.TypedOracleCompiler

/-! Exact, executable lowering of the #552 ideal public-mode interaction to
raw-key oracle calls. Simulator calls and construction calls share the same
oracle. Bounded sampling stops only on actual fuel exhaustion. The semantic
bridge and accounting equations are proved; caller-supplied Counts and the
primitive simulator budget remain explicit. -/
namespace Whir.DuplexRawProgram
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler

namespace ROProgram
variable {Q : Nat} {R S : Type}

def bind : DuplexModeGame.ROProgram Q R → (R → DuplexModeGame.ROProgram Q S) → DuplexModeGame.ROProgram Q S
  | .done r, f => f r
  | .ask key next, f => .ask key (fun a => bind (next a) f)

def map (f : R → S) : DuplexModeGame.ROProgram Q R → DuplexModeGame.ROProgram Q S
  | .done r => .done (f r)
  | .ask key next => .ask key (fun a => map f (next a))

@[simp] theorem run_bind (ro : RawKey Q → Digest32) (p : DuplexModeGame.ROProgram Q R)
    (f : R → DuplexModeGame.ROProgram Q S) :
    runRO ro (bind p f) = ((runRO ro (f (runRO ro p).1)).1,
      (runRO ro p).2 + (runRO ro (f (runRO ro p).1)).2) := by
  induction p with
  | done r => simp [bind, runRO]
  | ask key next ih => simp [bind, runRO, ih, Nat.add_assoc, Nat.add_comm]

@[simp] theorem run_map (ro : RawKey Q → Digest32) (f : R → S) (p : DuplexModeGame.ROProgram Q R) :
    runRO ro (map f p) = (f (runRO ro p).1, (runRO ro p).2) := by
  induction p with
  | done => rfl
  | ask key next ih => simp [map, runRO, ih]
end ROProgram

def observe {R : Type} (q : Query) (answer : Digest32) (v : View R) : View R :=
  ⟨⟨q,answer⟩ :: v.observations,v.result⟩

/-- Flatten the actual ideal interpreter, including its private simulator state.
The returned value exposes exactly the public view, never simulator state. -/
def compileIdeal {Q : Nat} {Seed State Result : Type} (sim : Simulator Q Seed State)
    (iv : Digest32) (state : State) :
    (p : Program Result) → (remaining : Nat) → remaining ≤ Q → Counts remaining p → DuplexModeGame.ROProgram Q (View Result)
  | .done result, _, _, _ => .done ⟨[],result⟩
  | .ask (.primitive purpose input) next, remaining, cap, counted =>
    ROProgram.bind (sim.answer state input) fun answer =>
      ROProgram.map (observe (.primitive purpose input) answer.2)
        (compileIdeal sim iv answer.1 (next answer.2) (remaining-1) (by omega) (counted.2 _))
  | .ask (.construction q valid) next, remaining, cap, counted =>
    .ask (constructionKey Q iv q (counted.1.trans cap)) fun answer =>
      ROProgram.map (observe (.construction q valid) answer)
        (compileIdeal sim iv state (next answer) (remaining-pathCost q) (by omega) (counted.2 _))

/-- Both the value and exact raw-call count are preserved. Every construction
occurrence contributes one raw call, and every simulator ask is retained. -/
theorem run_compileIdeal {Q : Nat} {Seed State Result : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) (p : Program Result)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p) :
    runRO ro (compileIdeal sim iv state p remaining cap counted) =
      ((runIdeal sim ro iv state p remaining cap counted).view,
       (runIdeal sim ro iv state p remaining cap counted).constructionRequests +
       (runIdeal sim ro iv state p remaining cap counted).simulatorQueries) := by
  induction p generalizing state remaining with
  | done result => rfl
  | ask q next ih =>
    cases q with
    | primitive purpose input =>
      have h := ih (runRO ro (sim.answer state input)).1.2
        (runRO ro (sim.answer state input)).1.1 (remaining-1) (by omega) (counted.2 _)
      simp only [compileIdeal, ROProgram.run_bind, ROProgram.run_map, h, runIdeal, prepend, observe]
      simp [Nat.add_left_comm]
    | construction q valid =>
      have h := ih (ro (constructionKey Q iv q (counted.1.trans cap))) state
        (remaining-pathCost q) (by omega) (counted.2 _)
      simp only [compileIdeal, runRO, ROProgram.run_map, h, runIdeal, prepend, observe]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem pathCost_pos (q : Coordinate) : 1 ≤ pathCost q := by
  simp [pathCost, DuplexEncoding.plan]

/-- Construction RO calls do not disappear when a coordinate is repeated. -/
theorem constructionRequests_le {Q : Nat} {Seed State Result : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) (p : Program Result)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p) :
    (runIdeal sim ro iv state p remaining cap counted).constructionRequests ≤ remaining := by
  induction p generalizing state remaining with
  | done result => simp [runIdeal]
  | ask q next ih =>
    cases q with
    | primitive purpose input =>
      have h := ih (runRO ro (sim.answer state input)).1.2
        (runRO ro (sim.answer state input)).1.1 (remaining-1) (by omega) (counted.2 _)
      simp only [runIdeal, prepend]
      omega
    | construction q valid =>
      have h := ih (ro (constructionKey Q iv q (counted.1.trans cap))) state
        (remaining-pathCost q) (by omega) (counted.2 _)
      have hp := pathCost_pos q
      have hc : pathCost q ≤ remaining := counted.1
      simp only [runIdeal, prepend]
      omega

/-- The two budgets are distinct: Q real primitive calls and Q simulator RO
calls imply at most 2Q total ideal raw calls, not at most Q. -/
theorem compileIdeal_calls_le {Q : Nat} {Seed State Result : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) (p : Program Result)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p)
    (simulatorBound : (runIdeal sim ro iv state p remaining cap counted).simulatorQueries ≤ Q) :
    (runRO ro (compileIdeal sim iv state p remaining cap counted)).2 ≤ 2*Q := by
  rw [run_compileIdeal]
  have h := constructionRequests_le sim ro iv state p remaining cap counted
  dsimp only
  omega

/-- Fuel belongs to raw calls, including duplicate keys and private simulator
calls. Exhaustion returns none and performs no additional oracle request. -/
def stop {Q : Nat} {R : Type} : (fuel : Nat) → DuplexModeGame.ROProgram Q R →
    Sampling (RawKey Q) (fun _ => Digest32) (Option R) fuel
  | _, .done r => .ret (some r)
  | 0, .ask _ _ => .ret none
  | fuel+1, .ask key next => .draw key (fun answer => stop fuel (next answer))

theorem eval_stop {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (fuel : Nat) (p : DuplexModeGame.ROProgram Q R) :
    Sampling.eval ro (stop fuel p) =
      if (runRO ro p).2 ≤ fuel then some (runRO ro p).1 else none := by
  induction fuel generalizing p with
  | zero => cases p <;> simp [stop, Sampling.eval, runRO]
  | succ fuel ih =>
    cases p with
    | done r => simp [stop, Sampling.eval, runRO]
    | ask key next => simpa [stop, Sampling.eval, runRO] using ih (next (ro key))

theorem stop_exact {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (fuel : Nat) (p : DuplexModeGame.ROProgram Q R) (counted : (runRO ro p).2 ≤ fuel) :
    Sampling.eval ro (stop fuel p) = some (runRO ro p).1 := by
  simp only [eval_stop, counted, ↓reduceIte]

theorem stop_exhausted {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (fuel : Nat) (p : DuplexModeGame.ROProgram Q R) :
    Sampling.eval ro (stop fuel p) = none ↔ fuel < (runRO ro p).2 := by
  rw [eval_stop]
  split_ifs <;> simp_all

/-- Operational trace length is exactly the number of raw calls executed before
termination or stopping. Duplicate keys are not erased by this compiler. -/
theorem execute_stop_length {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (fuel : Nat) (p : DuplexModeGame.ROProgram Q R) :
    (Sampling.execute ro (stop fuel p)).2.length = min fuel (runRO ro p).2 := by
  induction fuel generalizing p with
  | zero => cases p <;> simp [stop, Sampling.execute, runRO]
  | succ fuel ih =>
    cases p with
    | done r => simp [stop, Sampling.execute, runRO]
    | ask key next =>
      simp only [stop, Sampling.execute, List.length_cons, runRO]
      rw [ih]
      omega

theorem bounded_compileIdeal_exact {Q : Nat} {Seed State Result : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) (p : Program Result)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p)
    (simulatorBound : (runIdeal sim ro iv state p remaining cap counted).simulatorQueries ≤ Q) :
    Sampling.eval ro (stop (2*Q) (compileIdeal sim iv state p remaining cap counted)) =
      some (runIdeal sim ro iv state p remaining cap counted).view := by
  rw [stop_exact ro _ _ (compileIdeal_calls_le sim ro iv state p remaining cap counted simulatorBound)]
  rw [run_compileIdeal]

end Whir.DuplexRawProgram
