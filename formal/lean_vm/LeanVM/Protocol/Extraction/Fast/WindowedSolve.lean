module

public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant
public import LeanVM.Protocol.Extraction.Fast.Karatsuba
public import LeanVM.Protocol.Extraction.Fast.PMBasis.PopovCore
public import LeanVM.Protocol.Extraction.Fast.FFT.PlannedEval

/-!
# The certified window and the PM-basis context on evaluation-domain products

The pieces of the lanes' non-adaptive solver (`certifiedModularSolutionBasisContext`,
`CertifiedSolve.lean`) that are not the solve itself:

* `solveWindow`: the certified window, the caller's degree bound (the Guruswami–Sudan
  interpolation passes its weighted degree `W`), else the full pivot window;
* the PM-basis context, `popovEvalPMBasisContext T mulCtx lowCtx 1`: the ordered-weak-Popov
  PM-basis (`Popov.popovRuntime`: the leaf sorted by pivot, no root pass) at leaf cutoff `1`, its
  matrix products on the evaluation domain of a point transform `T`, the plan built once per
  product (`FFT.mulEvalP`), proved equal to popov's runtime (`popovEvalRuntime_eq`), so popov's
  soundness and shifted minimality carry over.
-/

namespace LeanVM.Extraction.Fast

open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The certified window: the caller's degree bound, else the full pivot window. -/
@[expose] def solveWindow (equation : ModularEquation F) (shift : Array Nat)
    (degreeBound? : Option Nat) : Nat :=
  degreeBound?.getD (fullWindowDegreeBound equation shift)

/-! ## The PM-basis contexts

The target: the ordered-weak-Popov PM-basis (`Popov.popovRuntime`, the leaf sorted by pivot, its
core returned with no root pass) with its two matrix products on the evaluation domains of a
point transform, each product's plan built once (`FFT.mulEvalP`, `FFT.mulTruncEvalP`), leaf
cutoff `1`: `popovEvalRuntime`, proved equal
to `Popov.popovRuntime` at every composition cutoff (`popovEvalRuntime_eq`: the products are equal
as functions), so popov's soundness and shifted minimality carry over
(`popovEvalPMBasisContext`). -/

/-- **The ordered-weak-Popov PM-basis runtime on evaluation-domain products.** -/
@[expose] def popovEvalRuntime {Plan : Type} (T : FFT.PointTransform F Plan)
    (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F) (leafCutoff : Nat) : PMBasisRuntime F where
  mulContext := mulCtx
  lowMulContext := lowCtx
  composeBasis := FFT.mulEvalP T mulCtx
  residualProduct := FFT.mulTruncEvalP T mulCtx
  leafCutoff := leafCutoff
  leafBasis := Popov.popovLeafBasis

/-- **It is popov's runtime**, at every composition cutoff. -/
theorem popovEvalRuntime_eq {Plan : Type} (T : FFT.PointTransform F Plan) (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F) (leafCutoff composeLeafCutoff : Nat) :
    popovEvalRuntime T mulCtx lowCtx leafCutoff =
      Popov.popovRuntime mulCtx lowCtx leafCutoff composeLeafCutoff := by
  rw [popovEvalRuntime, Popov.popovRuntime, Popov.leafRuntime]
  congr 1
  · exact funext fun A ↦ funext fun B ↦ (FFT.mulEvalP_eq T mulCtx A B).trans
      (EvalMat.mulEval_eq_mulStrassenWith T.toEvalMat mulCtx lowCtx _ A B)
  · exact funext fun orders ↦ funext fun A ↦ funext fun B ↦
      (FFT.mulTruncEvalP_eq T mulCtx orders A B).trans
        (EvalMat.mulTruncEval_eq_mulTruncColumnStrassenWith T.toEvalMat mulCtx lowCtx _ orders A B)

/-- **The PM-basis context on `popovEvalRuntime`**: its basis the recursion's core (no root
pass), sound and shifted-minimal (popov's, through `popovEvalRuntime_eq`). -/
@[expose] def popovEvalPMBasisContext {Plan : Type} (T : FFT.PointTransform F Plan)
    (mulCtx : CPolynomial.MulContext F) (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff : Nat) : PMBasisContext F where
  runtime := popovEvalRuntime T mulCtx lowCtx leafCutoff
  basis problem shift := pmBasisWithFuelCore (popovEvalRuntime T mulCtx lowCtx leafCutoff)
    (pmBasisFuel problem) problem shift
  sound := by
    intro problem shift row hrow
    rw [popovEvalRuntime_eq T mulCtx lowCtx leafCutoff leafCutoff] at hrow
    exact (Popov.popovCorePMBasisContextWithLowAndCompose mulCtx lowCtx leafCutoff
      leafCutoff).sound problem shift row hrow
  complete_minimal := by
    intro problem shift row hpos hwf happrox hnz hwidth
    rw [popovEvalRuntime_eq T mulCtx lowCtx leafCutoff leafCutoff]
    exact (Popov.popovCorePMBasisContextWithLowAndCompose mulCtx lowCtx leafCutoff
      leafCutoff).complete_minimal problem shift row hpos hwf happrox hnz hwidth

end

end LeanVM.Extraction.Fast
