import Whir.PublicCompressionCoupling
import Whir.DuplexRawProgram

/-! Exact mixed-oracle lowering of the PINNED stateful public simulator.
Fallback seed coordinates and raw RO coordinates remain independent branches
of one finite oracle. Construction internals are deliberately not computed
in this public phase. This is a checked operational identity, not a DMV premise. -/
namespace Whir.PublicCompressionCouplingMixed
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler
open scoped BigOperators

abbrev Key (Q : Nat) := Sum Node (RawKey Q)
abbrev Computation (Q : Nat) (R : Type) (calls : Nat) := Sampling (Key Q) (fun _ => Digest32) R calls

namespace Computation
variable {Q calls : Nat} {R S : Type}

def map (f : R → S) {calls : Nat} : Computation Q R calls → Computation Q S calls
  | .ret r => .ret (f r)
  | .draw key next => .draw key (fun d => map f (next d))

@[simp] theorem eval_map (table : Key Q → Digest32) (f : R → S) (p : Computation Q R calls) :
    Sampling.eval table (map f p) = f (Sampling.eval table p) := by
  induction p with
  | ret => rfl
  | draw key next ih => exact ih (table key)
end Computation

def oracle {Q : Nat} (seed : DuplexPublicSimulator.Seed) (ro : RawKey Q → Digest32) :
    Key Q → Digest32
  | .inl input => seed input
  | .inr key => ro key

def tableEquiv (Q : Nat) : (Key Q → Digest32) ≃
    DuplexPublicSimulator.Seed × (RawKey Q → Digest32) where
  toFun table := (fun n => table (.inl n),fun key => table (.inr key))
  invFun pair := oracle pair.1 pair.2
  left_inv table := by funext key; cases key <;> rfl
  right_inv pair := rfl

/-- Lookup, recognition, and fallback are exactly those of simulator.answer.
The continuation receives no fallback-table or raw-table access. -/
def primitiveCalls (Q : Nat) (log : DuplexPublicSimulator.PublicLog) (input : Node) :
    Computation Q (DuplexPublicSimulator.PublicLog × Digest32) 1 :=
  match DuplexPublicSimulator.lookup log input with
  | some answer => .ret (DuplexPublicSimulator.observe log input answer,answer)
  | none =>
    match DuplexPublicSimulator.privateKey Q log input with
    | some key => .draw (.inr key) (fun answer =>
        .ret (DuplexPublicSimulator.observe log input answer,answer))
    | none => .draw (.inl input) (fun answer =>
        .ret (DuplexPublicSimulator.observe log input answer,answer))

theorem primitiveCalls_actual (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (log : DuplexPublicSimulator.PublicLog) (input : Node) :
    (runRO ro ((DuplexPublicSimulator.simulator Q).answer ⟨seed,log⟩ input)).1 =
      (⟨seed,(Sampling.eval (oracle seed ro) (primitiveCalls Q log input)).1⟩,
        (Sampling.eval (oracle seed ro) (primitiveCalls Q log input)).2) := by
  cases hit : DuplexPublicSimulator.lookup log input with
  | some answer => simp [DuplexPublicSimulator.simulator,primitiveCalls,hit,runRO,Sampling.eval]
  | none =>
    cases key : DuplexPublicSimulator.privateKey Q log input <;>
      simp [DuplexPublicSimulator.simulator,primitiveCalls,hit,key,runRO,Sampling.eval,oracle]

/-- Source Counts charges each complete path, although the ideal public phase
makes one raw lookup for a construction and no hidden-prefix seed lookups. -/
def compile (Q : Nat) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog) :
    (p : Program R) → (remaining : Nat) → remaining ≤ Q → Counts remaining p →
      Computation Q (View R) remaining
  | .done result, _, _, _ => .ret ⟨[],result⟩
  | .ask (.primitive purpose input) next, remaining, cap, counted =>
      Sampling.pad (n := 1+(remaining-1)) (m := remaining)
        (by have hc : 1 ≤ remaining := counted.1; omega)
        (Sampling.bind (primitiveCalls Q log input) (fun result =>
          Computation.map (DuplexRawProgram.observe (.primitive purpose input) result.2)
            (compile Q iv result.1 (next result.2) (remaining-1) (by omega) (counted.2 _))))
  | .ask (.construction coordinate valid) next, remaining, cap, counted =>
      Sampling.pad (n := remaining-pathCost coordinate+1) (m := remaining) (by
        have hc : pathCost coordinate ≤ remaining := counted.1
        have hp := DuplexRawProgram.pathCost_pos coordinate
        omega)
        (.draw (.inr (constructionKey Q iv coordinate (counted.1.trans cap))) (fun answer =>
          Computation.map (DuplexRawProgram.observe (.construction coordinate valid) answer)
            (compile Q iv log (next answer) (remaining-pathCost coordinate) (by omega) (counted.2 _))))

theorem compile_actual (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog)
    (p : Program R) (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p) :
    Sampling.eval (oracle seed ro) (compile Q iv log p remaining cap counted) =
      (runIdeal (DuplexPublicSimulator.simulator Q) ro iv ⟨seed,log⟩
        p remaining cap counted).view := by
  induction p generalizing log remaining with
  | done => rfl
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [compile,Sampling.eval_pad,Sampling.eval_bind,Computation.eval_map,
        runIdeal,prepend]
      simp only [primitiveCalls_actual]
      have ht := ih (Sampling.eval (oracle seed ro) (primitiveCalls Q log input)).2
        (Sampling.eval (oracle seed ro) (primitiveCalls Q log input)).1
        (remaining-1) (by omega) (counted.2 _)
      exact congrArg
        (DuplexRawProgram.observe (.primitive purpose input)
          (Sampling.eval (oracle seed ro) (primitiveCalls Q log input)).2) ht
    | construction coordinate valid =>
      simp only [compile,Sampling.eval_pad,Sampling.eval,Computation.eval_map,
        oracle,runIdeal,prepend]
      rw [ih]
      rfl

/-- Every observed query is charged by its source cost, not ideal lookup cost. -/
def viewCost {R : Type} (view : View R) : Nat :=
  (view.observations.map (fun observation => observation.query.cost)).sum

theorem runIdeal_viewCost (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog)
    (p : Program R) (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p) :
    viewCost (runIdeal (DuplexPublicSimulator.simulator Q) ro iv ⟨seed,log⟩
      p remaining cap counted).view ≤ remaining := by
  have costEq : ∀ (state : DuplexPublicSimulator.State) (p : Program R)
      (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p),
      viewCost (runIdeal (DuplexPublicSimulator.simulator Q) ro iv state
        p remaining cap counted).view =
      (runIdeal (DuplexPublicSimulator.simulator Q) ro iv state
        p remaining cap counted).primitiveCost := by
    intro state p
    induction p generalizing state with
    | done => intro remaining cap counted; rfl
    | ask query next ih =>
      intro remaining cap counted
      cases query <;> simp [runIdeal,prepend,viewCost]
      all_goals exact ih _ _ _ _ _
  rw [costEq]
  exact runIdeal_counts _ _ _ _ _ _ _ counted

#print axioms primitiveCalls_actual
#print axioms compile_actual
#print axioms runIdeal_viewCost
end Whir.PublicCompressionCouplingMixed
