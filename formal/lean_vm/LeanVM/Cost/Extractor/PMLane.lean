module

public import LeanVM.Cost.Extractor.PMSolve
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
import all CompPoly.Univariate.Vanishing
import all CompPoly.Univariate.Roots.Backend
import all CompPoly.Univariate.Roots.Context
import all CompPoly.Univariate.Roots.Extraction
import all CompPoly.Univariate.Roots.RootProduct
import all CompPoly.Univariate.Roots.Splitter
import all CompPoly.Univariate.Roots.Shoup
import all CompPoly.Bivariate.Basic
import all CompPoly.Bivariate.GuruswamiSudan.Root.Common
import all CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots
import all CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
import all CompPoly.Fields.Binary.BF64.Impl
import all CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Algorithm
import all CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness
import all LeanVM.Protocol.Extraction.Extractor
import all Init.Data.List.Sort.Basic
import all CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Basic
import all CompPoly.Univariate.CoefficientInterpolation

/-!
# The lanes' approximant-basis interpolation, compiled (stage 5): the lanes and the decoded stacks

The approximant-basis interpolation on `pmSolver` (`interpolateDistinctWith`: the vanishing
polynomial and the interpolant, the modular data, the windowed solve of stage 4, the least shifted
row normalized), then the chain of `Fast/LanePM.lean` up to the decoded stacks
(`gsRunDistinctWith`, `pruneUpToWith`, `decodeStacksDistinctPM`), Roth–Ruckenstein's search
(`prefixesNF`) and the lane filter reused from `GsRun.lean`.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Extraction.Fast.FFT
open CompPoly.PolynomialMatrix.Approximant

public section

cost_compile gsModuliC := CompPoly.GuruswamiSudan.ApproximantBasis.gsModuli fftMulContext

cost_compile modByMonicCachedC := modByMonicCached fftRawMulLowContext

cost_compile gsRelationColumnC := gsRelationColumnCached fftMulContext fftRawMulLowContext

cost_compile gsRelationMatrixC := gsRelationMatrixCached fftMulContext fftRawMulLowContext

cost_compile gsDataC := buildGSModularDataCached fftMulContext fftRawMulLowContext

cost_compile leastShiftedDegreeChoiceC := CompPoly.PolynomialMatrix.leastShiftedDegreeChoice? (F := K)

cost_compile ofCoeffRowC := CompPoly.CBivariate.ofCoeffRow (F := K)

cost_compile interpolatePMC := interpolateDistinctWith pmSolver

cost_compile gsRunPMC := gsRunDistinctWith pmSolver

cost_compile pruneUpToPMC := pruneUpToWith pmSolver

cost_compile decodeStacksPMC := decodeStacksDistinctPM

end

end LeanVM.Cost.Extractor
