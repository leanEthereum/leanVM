module

public import LeanVM.Protocol.Extraction.Fast.FFT.Transform
public import LeanVM.Protocol.Extraction.Fast.EvalMat.Product
public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis

/-!
# Evaluation-domain matrix products with the plan built once

EvalMat's products (`mulEval T mulCtx`, `mulTruncEval T mulCtx`, `EvalMat/Product.lean`) call
`T.fwd j` per entry and `T.inv j` per output entry; for a point transform `T`
(`T.toEvalMat`), each such call builds the plan `T.plan j` again. `mulEvalP T mulCtx` and
`mulTruncEvalP T mulCtx` are the same products with `let P := T.plan j` (and `2^j`) hoisted: the plan is
built once per matrix product. They are EvalMat's products **by definition**
(`mulEvalP_eq`, `mulTruncEvalP_eq`: `rfl`), so CompPoly's Strassen-product equalities carry
over.
-/

namespace LeanVM.Extraction.Fast.FFT

open CompPoly PolynomialMatrix Approximant LeanVM.Extraction.Fast.EvalMat

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] {Plan : Type}

/-- The transforms by the plan `P` of the entries `entry i k`, `i < rows`, `k < cols`. -/
@[expose] def transformEntriesP (T : PointTransform F Plan) (P : Plan) (rows cols : ℕ)
    (entry : ℕ → ℕ → CPolynomial F) : Array (Array (Array F)) :=
  Array.ofFn fun i : Fin rows ↦ Array.ofFn fun k : Fin cols ↦ T.fwdP P (entry i k)

/-- **`mulEval` with the plan built once.** -/
@[expose] def mulEvalP (T : PointTransform F Plan) (mulCtx : CPolynomial.MulContext F)
    (A B : PolynomialMatrix F) : PolynomialMatrix F :=
  let r := A.size
  let s := B.size
  let t := MatrixWidth B
  let j := ceilLog (maxEntryDegree A r s + maxEntryDegree B s t + 1)
  if j ≤ T.maxLog then
    let P := T.plan j
    let N := 2 ^ j
    let FA := transformEntriesP T P r s fun i k ↦ rowGet (A.getD i #[]) k
    let FB := transformEntriesP T P s t fun k c ↦ rowGet (B.getD k #[]) c
    ofFn r t fun i c ↦ T.invP P (evalDot N s (FA.getD i #[]) FB c)
  else mulWith mulCtx A B

theorem mulEvalP_eq (T : PointTransform F Plan) (mulCtx : CPolynomial.MulContext F)
    (A B : PolynomialMatrix F) : mulEvalP T mulCtx A B = mulEval T.toEvalMat mulCtx A B := rfl

/-- **`mulTruncEval` with the plan built once.** -/
@[expose] def mulTruncEvalP (T : PointTransform F Plan) (mulCtx : CPolynomial.MulContext F)
    (orders : Array ℕ) (A B : PolynomialMatrix F) : PolynomialMatrix F :=
  let r := A.size
  let s := B.size
  let t := MatrixWidth B
  let O := maxOrderOf orders t
  let j := ceilLog (min (maxEntryDegree A r s) (O - 1) + min (maxEntryDegree B s t) (O - 1) + 1)
  if j ≤ T.maxLog then
    let P := T.plan j
    let N := 2 ^ j
    let FA := transformEntriesP T P r s fun i k ↦ truncateX O (rowGet (A.getD i #[]) k)
    let FB := transformEntriesP T P s t fun k c ↦ truncateX O (rowGet (B.getD k #[]) c)
    ofFn r t fun i c ↦ truncateX (orders.getD c 0) (T.invP P (evalDot N s (FA.getD i #[]) FB c))
  else truncateColumns orders (mulWith mulCtx A B)

theorem mulTruncEvalP_eq (T : PointTransform F Plan) (mulCtx : CPolynomial.MulContext F)
    (orders : Array ℕ) (A B : PolynomialMatrix F) :
    mulTruncEvalP T mulCtx orders A B = mulTruncEval T.toEvalMat mulCtx orders A B := rfl

end

end LeanVM.Extraction.Fast.FFT
