module

public import LeanVM.Cost.Extractor.Rewrites
public import LeanVM.Protocol.Extraction.Fast.RootFinder
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

/-!
# The extractor, compiled: the roots in `K` of a polynomial

`rootsInFieldFast` (`Fast/RootFinder.lean`): the product of the linear factors (`rootProductFast`:
`X^q − X` modulo the polynomial by repeated squaring, a gcd), split by Shoup's trace
(`splitCandidatesFast`), the roots read off the linear factors.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction.Fast

public section

cost_compile rootsInFieldC := rootsInFieldFast

end

end LeanVM.Cost.Extractor
