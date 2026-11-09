module

public import LeanVM.Cost.Extractor.Roots
public import LeanVM.Protocol.Extraction.Fast.TruncNoFallback
import all CompPoly.LinearAlgebra.PolynomialMatrix.Shifted
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Context
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Raw.Modular
import all CompPoly.Univariate.Vanishing
import all CompPoly.Univariate.Context
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
import all CompPoly.Data.Array.Lemmas
import all Init.Data.Array.Basic
import all LeanVM.Cost.FastLib

import all CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Algorithm
import all CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness

/-!
# The extractor, compiled: Roth–Ruckenstein's search

`prefixesNF` (`Fast/TruncNoFallback.lean`): Roth–Ruckenstein's search truncated at precision
`W + 1`, with the root finder of `Roots.lean` (reused), the substitution by the butterfly Taylor
shift (`substituteBF`, `Fast/TaylorShift.lean`, its bodies compiled on demand). The lanes' runs
(`gsRunDistinctWith pmSolver`) are compiled in `PMLane.lean`, after the interpolation's stages.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction.Fast

public section

cost_compile prefixesNFC := prefixesNF fieldRootCtxFast


end

end LeanVM.Cost.Extractor
