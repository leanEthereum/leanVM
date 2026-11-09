module

public import LeanVM.Protocol.ToCompPoly.Multilinear
public import LeanVM.Parameters.Field
meta import LeanVM.Protocol.ToCompPoly.Multilinear
meta import LeanVM.Parameters.Field
meta import CompPoly.Multilinear.Basic

/-!
# Hypercube table tests

Compiled checks (`#guard`) over `K` of the generic identities on a two-variable table: cube
points read entries, the Lagrange basis sums to one, evaluation is the weighted sum, a Boolean
high coordinate selects a slice, and a placed table keeps its cube sum and picks up the
Lagrange weight of its slot. The last section derives two special cases a consumer may want
from the generic lemmas, to show they need no lemma of their own.
-/

namespace LeanVMTests.Protocol

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

/-- The table `[1, 2, 3, 4]` on two variables. -/
def tbl : CMlPolynomialEval K 2 := #v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4]

/-- An off-cube point. -/
def pt : Vector K 2 := #v[K.ofBits 5, K.ofBits 9]

-- A cube point reads the entry (`evalMle_boolVec`): index 2 is `(0, 1)`, the third entry.
#guard evalMle tbl (boolVec (⟨2, by decide⟩ : Fin (2 ^ 2))) = K.ofBits 3
-- The Lagrange basis sums to one off the cube (`sumCube_lagrangeBasis`).
#guard sumCube (lagrangeBasis pt) = 1
-- Evaluation is the weighted sum (`evalMle_eq_sumCube_hadamard`).
#guard evalMle tbl pt = sumCube (hadamard (lagrangeBasis pt) tbl)
-- A constant table extends to the constant (`evalMle_replicate`).
#guard evalMle (Vector.replicate (2 ^ 2) (K.ofBits 7 : K)) pt = K.ofBits 7
-- Selection (`evalMle_append_boolVec`): high coordinate `1` selects the slice `[3, 4]`.
#guard evalMle tbl (#v[(K.ofBits 7 : K)] ++ (boolVec (⟨1, by decide⟩ : Fin (2 ^ 1)) : Vector K 1)) =
  evalMle (#v[K.ofBits 3, K.ofBits 4] : CMlPolynomialEval K 1) #v[K.ofBits 7]
-- Mutation: high coordinate `0` selects the other slice, which answers differently.
#guard evalMle tbl (#v[(K.ofBits 7 : K)] ++ (boolVec (⟨0, by decide⟩ : Fin (2 ^ 1)) : Vector K 1)) ≠
  evalMle (#v[K.ofBits 3, K.ofBits 4] : CMlPolynomialEval K 1) #v[K.ofBits 7]

/-! ## Placing a table on a slice -/

-- The table at slot 2 of four: entries 4 and 5 of eight, zero elsewhere.
#guard (placeSlice (R := K) (k := 1) (m := 2) #v[K.ofBits 3, K.ofBits 4] ⟨2, by decide⟩).toList =
  [0, 0, 0, 0, K.ofBits 3, K.ofBits 4, 0, 0]
-- Reading the slot back returns the table; another slot is empty (`slice_placeSlice`).
#guard slice (k := 1) (m := 2)
    (placeSlice (#v[K.ofBits 3, K.ofBits 4] : CMlPolynomialEval K 1) (⟨2, by decide⟩ : Fin (2 ^ 2)))
    (⟨2, by decide⟩ : Fin (2 ^ 2)) = #v[K.ofBits 3, K.ofBits 4]
#guard slice (k := 1) (m := 2)
    (placeSlice (#v[K.ofBits 3, K.ofBits 4] : CMlPolynomialEval K 1) (⟨2, by decide⟩ : Fin (2 ^ 2)))
    (⟨1, by decide⟩ : Fin (2 ^ 2)) = #v[0, 0]
-- Placing keeps the cube sum, whatever the slot (`sumCube_placeSlice`).
#guard sumCube (placeSlice tbl (⟨1, by decide⟩ : Fin (2 ^ 1))) = sumCube tbl
#guard sumCube (placeSlice tbl (⟨0, by decide⟩ : Fin (2 ^ 1))) = sumCube tbl
-- Its extension is the table's, times the Lagrange weight of the slot (`evalMle_placeSlice`).
#guard evalMle (placeSlice tbl (⟨1, by decide⟩ : Fin (2 ^ 1))) (pt ++ #v[(K.ofBits 11 : K)]) =
  (lagrangeBasis (#v[(K.ofBits 11 : K)]))[1] * evalMle tbl pt
-- Mutation: the other slot carries the other weight.
#guard evalMle (placeSlice tbl (⟨0, by decide⟩ : Fin (2 ^ 1))) (pt ++ #v[(K.ofBits 11 : K)]) ≠
  evalMle (placeSlice tbl (⟨1, by decide⟩ : Fin (2 ^ 1))) (pt ++ #v[(K.ofBits 11 : K)])

/-! ## The two corners -/

#guard (boolVec (⟨0, by decide⟩ : Fin (2 ^ 3)) : Vector K 3) = #v[0, 0, 0]
#guard (boolVec (onesIndex 3) : Vector K 3) = #v[1, 1, 1]
-- The Lagrange basis at the corners: the product of the coordinates, and of their complements.
#guard (lagrangeBasis (#v[K.ofBits 5, K.ofBits 9, K.ofBits 11] : Vector K 3))[(onesIndex 3).val] = (K.ofBits 5) * (K.ofBits 9) * (K.ofBits 11)
#guard (lagrangeBasis (#v[K.ofBits 5, K.ofBits 9, K.ofBits 11] : Vector K 3))[0] = (1 - (K.ofBits 5)) * (1 - (K.ofBits 9)) * (1 - (K.ofBits 11))

/-! ## Special cases are corollaries

Evaluating at a point whose coordinates past the first `k` are all zero reads the first slice:
no lemma about such points is needed, the selection identity at index zero is that statement. -/

example {R : Type} [CommRing R] {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (z : Vector R k) :
    evalMle t (z ++ Vector.replicate m (0 : R)) =
      evalMle (slice t (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m))) z := by
  rw [← boolVec_zero, evalMle_append_boolVec]

-- On a table of two variables, at `(r, 0)`: the line through the first two entries.
#guard evalMle tbl ((#v[(K.ofBits 7 : K)] : Vector K 1) ++ Vector.replicate 1 (0: K)) =
  (1 - (K.ofBits 7)) * 1 + (K.ofBits 7) * (K.ofBits 2)
-- Mutation: at `(r, 1)` it is the line through the last two.
#guard evalMle tbl ((#v[(K.ofBits 7 : K)] : Vector K 1) ++ Vector.replicate 1 (1: K)) =
  (1 - (K.ofBits 7)) * (K.ofBits 3) + (K.ofBits 7) * (K.ofBits 4)

end
end LeanVMTests.Protocol
