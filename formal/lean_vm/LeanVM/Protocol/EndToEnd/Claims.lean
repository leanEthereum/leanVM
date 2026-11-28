/-
  LeanVM.Protocol.EndToEnd.Claims

  A stack claim's meaning, in the form the WHIR soundness proof reads it, and a weight that is the
  multilinear extension of its values on the cube.
-/

module

public import LeanVM.Protocol.Relation.Stack
public import Statement.Prover.Script

/-!
# The claims of the stacked opening

`StackClaim.Holds μ c q` is `Relation.StackClaimHolds c q` (`stackClaim_holds_iff`, by
definition) with the stack's cells written as `q.values.getD`, the form the WHIR soundness proof
(`Whir.Sound`) unfolds; `boolPoint` and `IsMultilinearFn` are `Tables`'.
-/

namespace LeanVM.Protocol.EndToEnd

open LeanVM.Parameters LeanVM.Protocol.Verifier

export LeanVM.Protocol.Tables (boolPoint IsMultilinearFn)

@[expose] public section

/-- The meaning of a stack claim: the weight's values on the cube, paired with the stack, give
the value. -/
def StackClaim.Holds (μ : ℕ) (c : StackClaim) (q : Column μ) : Prop :=
  ∑ x : Fin (2 ^ μ), c.1 (boolPoint μ x) * ofK (q.values.getD x 0) = c.2

/-- `StackClaim.Holds` is the relation's `StackClaimHolds`. -/
theorem stackClaim_holds_iff {μ : ℕ} {c : StackClaim} {q : Column μ} :
    StackClaim.Holds μ c q ↔ Relation.StackClaimHolds c q := Iff.rfl

end
end LeanVM.Protocol.EndToEnd
