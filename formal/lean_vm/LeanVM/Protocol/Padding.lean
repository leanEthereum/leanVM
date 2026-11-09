/-
  LeanVM.Protocol.Padding

  Back-loaded padding: a table lifted to a taller cube by the product of the new variables, so
  that tables of different heights share one sumcheck.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear

/-!
# Back-loaded padding

leanVM's tables have different heights and one sumcheck runs over all of them. A table on `k`
variables joins a cube of `k + m` variables multiplied by `∏_{c ≥ k} X_c`, the product of the
variables it does not have (specification §5.5): on the cube that product is one where the new
coordinates are all one and zero elsewhere, so the lifted table is the table placed on that one
slice. Its sum over the taller cube is the table's own sum (`sumCube_padHigh`), and its
extension is the table's extension times the product of the new coordinates
(`evalMle_padHigh`).

The slice is the protocol's choice. Placing a table on any slice is `placeSlice`, in
`ToCompPoly/Multilinear.lean`; `padHigh` is `placeSlice` at the all-ones index. Written
from the specification.

## Wrong readings excluded

* Copying the table into every slice of the taller cube multiplies its sum by `2 ^ m`, which is
  zero in characteristic two for `m ≥ 1`.
* The new variables are the high coordinates `k, …, k + m - 1`, not the low ones.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-- A table of `k` variables lifted to `k + m` variables by `∏_{c ≥ k} X_c`: its entries sit
where the high coordinates are all ones, and everything else is zero. -/
def padHigh {k : ℕ} (t : CMlPolynomialEval R k) (m : ℕ) : CMlPolynomialEval R (k + m) :=
  placeSlice t (onesIndex m)

end
end LeanVM.Protocol
