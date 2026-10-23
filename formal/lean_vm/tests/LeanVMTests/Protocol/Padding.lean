/-
  LeanVMTests.Protocol.Padding

  Controls for back-loaded padding: which slice the table lands on, and what copying the table
  would give instead.
-/

module

public import LeanVM.Protocol.Padding
public import LeanVM.Parameters.Field
meta import LeanVM.Protocol.Padding
meta import LeanVM.Parameters.Field
meta import CompPoly.Multilinear.Basic

/-!
# Back-loaded padding controls

The table is lifted by two variables, so that the all-ones slice (index 3) differs from the
top-bit slice (index 2) and from index 1. Copying the table into every slice is the mutation:
in characteristic two its sum is zero.
-/

namespace LeanVMTests.Protocol

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

/-- The table `[3, 5]` on one variable. -/
def short : CMlPolynomialEval K 1 := #v[K.ofBits 3, K.ofBits 5]

-- Lifted by two variables, it sits on the last slice of four.
#guard padHigh short 2 = #v[0, 0, 0, 0, 0, 0, K.ofBits 3, K.ofBits 5]
-- The lift keeps the sum over the cube.
#guard sumCube (padHigh short 2) = sumCube short
-- Its extension is the table's, times the product of the two new coordinates.
#guard evalMle (padHigh short 2) ((#v[K.ofBits 7] : Vector K 1) ++ (#v[K.ofBits 11, K.ofBits 13] : Vector K 2)) =
  evalMle short #v[K.ofBits 7] * ((K.ofBits 11) * (K.ofBits 13))
-- Mutation: one new coordinate alone is not the factor.
#guard evalMle (padHigh short 2) ((#v[K.ofBits 7] : Vector K 1) ++ (#v[K.ofBits 11, K.ofBits 13] : Vector K 2)) ≠
  evalMle short #v[K.ofBits 7] * (K.ofBits 13)

/-- The table copied into every slice: lifting by nothing. -/
def copied : CMlPolynomialEval K 3 := #v[K.ofBits 3, K.ofBits 5, K.ofBits 3, K.ofBits 5, K.ofBits 3, K.ofBits 5, K.ofBits 3, K.ofBits 5]

-- Its sum is four times the table's, zero in characteristic two.
#guard sumCube copied = 0
#guard sumCube copied ≠ sumCube short

end
end LeanVMTests.Protocol
