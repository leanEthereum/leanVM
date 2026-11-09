module

public import LeanVM.Cost.Extractor.PMCore
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

import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.ModularEquation.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PartialLinearization

/-!
# The lanes' approximant-basis interpolation, compiled (stage 4): the certified modular solve

`certifiedSolutionBasis` (`Fast/CertifiedSolve.lean`, `pmSolver`'s) on the additive-FFT
remainders and the PM-basis of stage 3: the exact-nullspace problem over the window, one PM-basis
call, the rows certified by a size and a degree read (no product), their principal parts.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Extraction.Fast.FFT
open CompPoly.PolynomialMatrix.Approximant

public section

cost_compile certifiedGuardC := certifiedGuard (F := K)

cost_compile exactNullspaceShiftC := exactNullspaceShift

cost_compile fullWindowProblemC := fullWindowExactNullspaceProblem fftModContext

cost_compile certifiedRowC := certifiedRow (F := K)

cost_compile principalSolutionRowsC := principalSolutionRows (F := K)

cost_compile certifiedSolveC := certifiedSolutionBasis fftModContext
  (popovEvalPMBasisContext novelTransform fftMulContext fftMulLowContext 1)

end

end LeanVM.Cost.Extractor
