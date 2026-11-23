/-
  LeanVM.Protocol.ToVCVio.PrEvent

  An event's probability is at most any bound of at least one. Candidate for VCVio.
-/

module

public import PolyFun.Control.Monad.Measure.Event

/-!
# A trivial probability bound

`prEvent_le_of_one_le`: an event's probability is at most any bound of at least `1`. The end
statements state their bounds for every query count, and past the count where a bound reaches `1`
this lemma proves them.
-/

open scoped ENNReal

@[expose] public section

/-- An event's probability is at most any bound of at least `1`. -/
theorem prEvent_le_of_one_le {m : Type → Type*} [EvalDistSemantics m] (mx : m Prop) {ε : ℝ≥0∞}
    (h : 1 ≤ ε) : prEvent mx ≤ ε :=
  (prEvent_le_one mx).trans h

end
