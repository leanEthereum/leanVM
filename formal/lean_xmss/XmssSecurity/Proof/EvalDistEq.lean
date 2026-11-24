module

public import Common.EvalDistEq

@[expose] public section

/-! Elaboration aid for equality in distribution (`=ᵈ`); the generic facts are in `Common.EvalDistEq`. -/

/-- Elaborate both sides of `=ᵈ` against a common type, as `=` does, so a side whose monad is
only known from the other (a `do` block or `pure` in a `calc` step) elaborates. -/
macro_rules | `($a =ᵈ $b) => `(binrel% EvalDistEq $a $b)
