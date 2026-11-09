module

public import LeanVM.Cost.Extractor.PMFFT
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

/-!
# The lanes' approximant-basis interpolation, compiled (stage 2): products of polynomial matrices

On the additive FFT's evaluation domain, each product's plan built once (`FFT.mulEvalP`,
`FFT.mulTruncEvalP` at `novelTransform`): every entry transformed once, the pointwise dot
products (`EvalMat.evalDot`), each result interpolated.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Extraction.Fast.FFT

public section

cost_compile evalDotC := EvalMat.evalDot (F := K)

cost_compile transformEntriesPC := FFT.transformEntriesP novelTransform

cost_compile mulEvalPC := FFT.mulEvalP novelTransform fftMulContext

cost_compile mulTruncEvalPC := FFT.mulTruncEvalP novelTransform fftMulContext

end

end LeanVM.Cost.Extractor
