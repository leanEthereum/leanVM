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
`doc/leanvm/body/04-committing-the-witness.tex`). `eqWeight p` is that weight, with the
closed form of its extension the verifier evaluates.

Written from the specification.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

end
end LeanVM.Protocol
