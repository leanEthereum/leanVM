module

public import LeanVM.Cost.Library
public import CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Data.Array.Lemmas
import all Init.Data.Array.Basic

/-!
# Tests: a sample, CompPoly's `addRaw` over `K`, compiled

CompPoly's `addRaw` (github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly
Contributors"; nothing of it is copied): pad both coefficient arrays to the longer one
(`Array.matchSize`), add entrywise (`Array.zipWith`, compiled through `List.zipWith`). One
`cost_compile` line: the code, the spec (`addRawK.costSpec`) and the price's recurrence
(`addRawK.costEq`) are the compiler's.
-/

namespace LeanVMTests.Cost.Samples

open LeanVM.Cost LeanVM.Parameters

cost_compile addRawK := @CompPoly.CPolynomial.Raw.addRaw K _ _

end LeanVMTests.Cost.Samples
