module

public import LeanVM.Cost.Extractor.PMEval
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Context
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Raw.Modular
import all CompPoly.Univariate.Context
import all CompPoly.Data.Array.Lemmas
import all Init.Data.Array.Basic
import all LeanVM.Cost.FastLib

import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Operations

import all CompPoly.LinearAlgebra.PolynomialMatrix.Shifted
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeaf
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.Recursion
import all CompPoly.LinearAlgebra.Dense

/-!
# The lanes' approximant-basis interpolation, compiled (stage 3): the PM-basis

The ordered-weak-Popov PM-basis's recursion (`pmBasisWithFuelCore` at `popovEvalRuntime
novelTransform fftMulContext fftMulLowContext 1`: the leaf sorted by pivot, `Popov.popovLeafBasis`,
at order one; the two matrix products of stage 2).
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Extraction.Fast.FFT
open CompPoly.PolynomialMatrix.Approximant

public section

cost_compile maxOrderC := maxOrder (F := K)

cost_compile lowerOrdersC := lowerOrders (F := K)

cost_compile residualOrdersC := residualOrders (F := K)

cost_compile divXTruncC := CompPoly.PolynomialMatrix.divXTrunc (F := K)

cost_compile residualMatrixC := residualMatrixWithProduct (FFT.mulTruncEvalP novelTransform fftMulContext)

cost_compile updateShiftByRowsC := updateShiftByRows (F := K)

cost_compile compactNonzeroRowsC := compactNonzeroRows (F := K)

cost_compile popovLeafC := Popov.popovLeafBasis (F := K)

cost_compile pmCoreC measure fun fuel _ _ ↦ fuel := pmBasisWithFuelCore (popovEvalRuntime novelTransform fftMulContext fftMulLowContext 1)

end

end LeanVM.Cost.Extractor
