import Whir.RawOracleCoupling

/-! A causal allocation decorator freezes the selected label before sampling.
Labels are retained in the emitted draw trace, never rebuilt from final state. -/
namespace Whir.CausalAllocationLabels
open TypedOracleCompiler
open RawOracleCoupling (average_equiv)

universe u v w x y z

structure Decorator (State : Type u) (Key : Type v) (Answer : Key → Type w)
    (Label : Type x) (LabelAnswer : Label → Type y) where
  prepare : State → Key → State × Label
  answer : ∀ state key, Answer key ≃ LabelAnswer (prepare state key).2
  advance : State → (label : Label) → LabelAnswer label → State

namespace Decorator
variable {State : Type u} {Key : Type v} {Answer : Key → Type w}
variable {Label : Type x} {LabelAnswer : Label → Type y}
variable (decorator : Decorator State Key Answer Label LabelAnswer)

/-- Only the original requested answer reaches the original continuation.
`prepare` cannot inspect that answer; `advance` runs after its fresh sampling. -/
def decorate {R : Type z} {n} : Sampling Key Answer R n → State →
    Sampling Label LabelAnswer (R × State) n
  | .ret result, state => .ret (result,state)
  | .draw key next, state =>
    let prepared := decorator.prepare state key
    .draw prepared.2 (fun answer =>
      decorate (next ((decorator.answer state key).symm answer))
        (decorator.advance prepared.1 prepared.2 answer))

/-- Executable causal trace translation. The original full allocation trace is
an analysis object, not an additional input available to the strategy. -/
def traceRecode : State → List (Sigma Answer) → List (Sigma LabelAnswer) × State
  | state, [] => ([],state)
  | state, ⟨key,answer⟩ :: rest =>
    let prepared := decorator.prepare state key
    let labeled := decorator.answer state key answer
    let after := decorator.advance prepared.1 prepared.2 labeled
    let tail := traceRecode after rest
    (⟨prepared.2,labeled⟩ :: tail.1,tail.2)

/-- This relation exposes the exact chronological state transitions, including
both the before-draw preparation and after-answer advancement. -/
inductive Evolves : State → List (Sigma Answer) → List (Sigma LabelAnswer) → State → Prop where
  | nil (state : State) : Evolves state [] [] state
  | cons (state : State) (key : Key) (answer : Answer key) {raw labeled final}
      (tail : Evolves
        (decorator.advance (decorator.prepare state key).1 (decorator.prepare state key).2
          (decorator.answer state key answer)) raw labeled final) :
      Evolves state (⟨key,answer⟩ :: raw)
        (⟨(decorator.prepare state key).2,decorator.answer state key answer⟩ :: labeled) final

 theorem traceRecode_evolves (state : State) (raw : List (Sigma Answer)) :
    decorator.Evolves state raw (decorator.traceRecode state raw).1
      (decorator.traceRecode state raw).2 := by
  induction raw generalizing state with
  | nil => exact .nil state
  | cons entry rest ih => exact .cons state entry.1 entry.2 (ih _)

 theorem Evolves.exact {state raw labeled final}
    (evolution : decorator.Evolves state raw labeled final) :
    decorator.traceRecode state raw = (labeled,final) := by
  induction evolution with
  | nil => rfl
  | cons state key answer tail ih => simp only [traceRecode, ih]

 theorem traceRecode_length (state : State) (raw : List (Sigma Answer)) :
    (decorator.traceRecode state raw).1.length = raw.length := by
  induction raw generalizing state with
  | nil => rfl
  | cons entry rest ih => simp only [traceRecode, List.length_cons, ih]

/-- Exact operational correspondence for every branch, including early stops.
A label is the one selected at its allocation time, not a final-state lookup. -/
theorem runs_iff {R : Type z} {n} (program : Sampling Key Answer R n) (state : State)
    (labeled : List (Sigma LabelAnswer)) (result : R) (final : State) :
    Sampling.Runs (decorator.decorate program state) labeled (result,final) ↔
      ∃ raw, Sampling.Runs program raw result ∧
        decorator.traceRecode state raw = (labeled,final) := by
  induction program generalizing state labeled final with
  | ret value =>
    constructor
    · intro run
      cases run
      exact ⟨[],.ret _,rfl⟩
    · rintro ⟨raw,run,equal⟩
      cases run
      cases equal
      exact .ret _
  | draw key next ih =>
    constructor
    · intro run
      cases run with
      | draw answer run =>
        obtain ⟨raw,original,equal⟩ := (ih _ _ _ _).mp run
        refine ⟨⟨key,(decorator.answer state key).symm answer⟩ :: raw,
          .draw _ original,?_⟩
        simp only [traceRecode, Equiv.apply_symm_apply, equal]
    · rintro ⟨raw,original,equal⟩
      cases original with
      | draw answer original =>
        simp only [traceRecode] at equal
        cases equal
        apply Sampling.Runs.draw (decorator.answer state key answer)
        simpa only [Equiv.symm_apply_apply] using
          (ih answer _ _ _).mpr ⟨_,original,rfl⟩

 theorem runs_causal {R : Type z} {n} (program : Sampling Key Answer R n) (state : State)
    {labeled result final} (run : Sampling.Runs (decorator.decorate program state) labeled (result,final)) :
    ∃ raw, Sampling.Runs program raw result ∧ decorator.Evolves state raw labeled final := by
  obtain ⟨raw,original,equal⟩ := (decorator.runs_iff program state labeled result final).mp run
  refine ⟨raw,original,?_⟩
  have evolution := decorator.traceRecode_evolves state raw
  rw [equal] at evolution
  exact evolution

 theorem all_branch_cap {R : Type z} {n} (program : Sampling Key Answer R n) (state : State)
    {trace result} (run : Sampling.Runs (decorator.decorate program state) trace result) :
    trace.length ≤ n := run.length_le

variable [∀ key, Fintype (Answer key)]
variable [∀ label, Fintype (LabelAnswer label)]

/-- Exact every-payoff distribution preservation for the original result.
The decorator's private adaptive state is not passed to the original strategy. -/
theorem expectation {R : Type z} {n} (program : Sampling Key Answer R n) (state : State)
    (payoff : R → ℚ) :
    Sampling.expectation (fun result => payoff result.1) (decorator.decorate program state) =
      Sampling.expectation payoff program := by
  induction program generalizing state with
  | ret result => rfl
  | draw key next ih =>
    simp only [decorate, Sampling.expectation, ih]
    exact average_equiv (decorator.answer state key).symm
      (fun answer => Sampling.expectation payoff (next answer))

end Decorator
end Whir.CausalAllocationLabels
