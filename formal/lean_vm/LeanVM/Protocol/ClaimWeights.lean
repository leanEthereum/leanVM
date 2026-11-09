/-
  LeanVM.Protocol.ClaimWeights

  A claim on one column of the stack is a weighted claim on the stack, the weight being the
  equality kernel at the claim's point lifted through the layout.
-/

module

public import LeanVM.Protocol.Spine.Seams

/-!
# Column claims as weighted claims

The opening argument works on one kind of claim, `⟨W, q⟩ = c` for a weight `W` on the stack. A
claim `P̃(z) = c` on a column joins that pool through the stacking identity: with `p` the point
`z` lifted through the layout, `P̃(z) = q̃(p) = Σ_w eq(p, w) q(w)` (specification §4.1,
`doc/leanvm/body/04-committing-the-witness.tex:12-22`). `eqWeight p` is that weight, with the
closed form of its extension the verifier evaluates, and `ColumnClaim.holds_iff_weighted` is the
step, for any instance and any column read off the stack (a derived column, `I.derived c ≠
none`, is not on the stack). It uses the reading law of the instance's
layout and nothing about how the layout was built.

Written from the specification.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

/-- A claim on a column read off the stack (not derived) is the weighted claim on the stack
whose weight is the equality kernel at the claim's point lifted through the layout. -/
theorem ColumnClaim.holds_iff_weighted {I : M3Instance} (q : Column I.μ) (c : ColumnClaim I)
    (hc : I.derived c.col = none) :
    c.Holds q ↔
      WeightedClaim.Holds q ⟨eqWeight (I.layout.extend c.col c.point), c.value⟩ := by
  unfold ColumnClaim.Holds WeightedClaim.Holds
  rw [Weight.pair_eqWeight, ← I.layout.read_eval, M3Instance.column, hc]
  rfl

end
end LeanVM.Protocol
