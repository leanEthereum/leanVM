import Sphincs.BridgeInterp

/-! Bookkeeping for linear potentials on the interpreted comparison: the number of message-digest
queries of a trace, and the expected final payoff of a state once its unexposed coordinates are
completed. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- Number of message-digest queries of a trace. -/
noncomputable def digestCount (entries : List (Entry D)) : ℕ :=
  (entries.filter fun entry => match entry with
    | .inl input => decide (tg.digest input)
    | .inr _ => false).length

omit [Fintype ι] [SampleableType R] in
theorem digestCount_append (first second : List (Entry D)) :
    digestCount tg (first ++ second) = digestCount tg first + digestCount tg second := by
  simp [digestCount, List.filter_append]

/-- Expected final payoff of a state, once its unexposed coordinates are completed. -/
noncomputable def endValue (payoff : (ι → Digest) → DebtState D R ι → ℝ≥0∞) (state : DebtState D R ι) :
    ℝ≥0∞ :=
  ∑' table, Pr[= table | completion state.known] * payoff table state

end Sphincs.Security.HiddenDebt
