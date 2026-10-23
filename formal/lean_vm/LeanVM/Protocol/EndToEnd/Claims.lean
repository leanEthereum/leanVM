/-
  LeanVM.Protocol.EndToEnd.Claims

  What the verifier program's claims say about a stack: the semantics of a stack claim (a weight
  function and a value) and of a column claim placed on the stack by the layout. The interface
  between the front phases' bridges and the opening's.
-/

module

public import LeanVM.Protocol.Verifier
public import LeanVM.Protocol.Field

/-!
# The claims of the verifier program

The verifier program (`LeanVM.Protocol.Verifier`) accumulates claims about the committed
stack as data: column claims (`Verifier.ColumnClaim`: a global column, a point, a value), placed on
the stack by the layout (`ColumnClaim.onStack`), and the ring-switching claim, each a
`StackClaim`: a weight function on points of the stack's cube and a value. The opening batches
them and WHIR checks the batch against the committed word.

`StackClaim.Holds μ c q` is the claim's meaning for a stack `q` on `μ` variables: the inner product
of the weight's values on the cube with the stack is the value. `boolPoint μ x` is the cube point
of index `x`, bit `0` first, as the verifier writes points (`eq_eval`, `_selector_point`,
`verifier.py:256-318`). A weight function means what WHIR checks of it only if it is the
multilinear extension of its values on the cube (`IsMultilinearFn`): WHIR's terminal check
evaluates it at a random point.

The front phases' bridges end on "no candidate of the commitment satisfies the claims", in these
terms; the opening's bridge starts from it.
-/

namespace LeanVM.Protocol.EndToEnd

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The cube point of index `x` on `μ` coordinates, bit `0` first, with coordinates `0`/`1`
in `E`. -/
def boolPoint (μ x : ℕ) : List E :=
  (List.range μ).map fun i ↦ if x.testBit i then 1 else 0

/-- The meaning of a stack claim: the weight's values on the cube, paired with the stack, give
the value. -/
def StackClaim.Holds (μ : ℕ) (c : StackClaim) (q : Column μ) : Prop :=
  ∑ x : Fin (2 ^ μ), c.1 (boolPoint μ x) * ofK (q.values.getD x 0) = c.2

/-- A weight function is the multilinear extension of its values on the cube: at every point of
`μ` coordinates it is `Σ_x w(x) · eq(x, point)`. -/
def IsMultilinearFn (μ : ℕ) (w : List E → E) : Prop :=
  ∀ point : List E, point.length = μ →
    w point = ∑ x : Fin (2 ^ μ), w (boolPoint μ x) * eqEval (boolPoint μ x) point

/-- Every column claim of a list holds of the stack, each placed on the stack by the layout. -/
def ColumnClaimsHold (layout : Layout) (cs : List ColumnClaim) (q : Column layout.stackLog) :
    Prop :=
  ∀ c ∈ cs, StackClaim.Holds layout.stackLog (c.onStack layout) q

end
end LeanVM.Protocol.EndToEnd
