import LeanVM.Protocol.ToCompPoly.ProductTree
import LeanVM.Protocol.ToCompPoly.PartialSum

/-!
# Product tree and partial sum tests

Over the integers, where every value is legible.

* **The tree.** `contract` multiplies adjacent entries; `layerTable` reaches the leaves at `μ`,
  the root at `0`, and each level is the contraction of the one below. The root is the product of
  the leaves.
* **The descendants.** `childIndex ρ c x` is `c + 2^ρ x`, and `childPoint` puts the descendant's
  bits in the low coordinates: the point `(1, 1, 9)` and not `(9, 1, 1)`. A node two levels up is
  the product of its four descendants, and the layer identity holds at a non-Boolean point.
* **Partial sums.** With nothing fixed, the partial sum is the extension of the table; fixing a
  coordinate splits it by `1 - r_j` and `r_j`; with everything fixed it is the value.
A plain file, so `#guard` evaluates the compiled definitions.
-/

namespace LeanVMTests.Protocol.ProductTree

open LeanVM.Protocol CompPoly CMlPolynomialEval

/-! ## The tree -/

/-- Four leaves. -/
def leaves : CMlPolynomialEval ℤ 2 := #v[2, 3, 5, 7]

#guard (contract leaves).toList = [6, 35]
#guard (layerTable leaves 2).toList = [2, 3, 5, 7]
#guard (layerTable leaves 1).toList = [6, 35]
#guard (layerTable leaves 0).toList = [210]
-- Past the leaves the level is a table of ones: the definition is total.
#guard (layerTable leaves 3).toList = [1, 1, 1, 1, 1, 1, 1, 1]
-- The root is the product of every leaf.
#guard (layerTable leaves 0)[0] = 2 * 3 * 5 * 7

/-! ## The descendants -/

/-- Eight leaves. -/
def eight : CMlPolynomialEval ℤ 3 := #v[2, 3, 5, 7, 11, 13, 17, 19]

-- `childIndex ρ c x = c + 2^ρ x`: the descendants of node `1`, two levels down, are `4, 5, 6, 7`.
#guard (List.ofFn fun c : Fin 4 ↦ (childIndex 2 (n := 1) c 1).val) = [4, 5, 6, 7]
-- The descendant's bits come first, low bit first: descendant `3 = (1, 1)` of the point `9`.
#guard (childPoint 2 (3 : Fin 4) (#v[9] : Vector ℤ 1)).toList = [1, 1, 9]
#guard (childPoint 2 (3 : Fin 4) (#v[9] : Vector ℤ 1)).toList ≠ [9, 1, 1]
#guard (childPoint 2 (1 : Fin 4) (#v[9] : Vector ℤ 1)).toList = [1, 0, 9]
-- Two levels up, node `1` is the product of leaves `4, 5, 6, 7`.
#guard (contractPow 2 eight).toList = [2 * 3 * 5 * 7, 11 * 13 * 17 * 19]
#guard (contractPow 2 eight)[1] = ∏ c : Fin 4, eight[childIndex 2 (n := 1) c 1]

/-- A non-Boolean point. -/
def r : Vector ℤ 1 := #v[4]

-- The layer identity at `r`: the contracted level's extension is the eq-weighted sum of the
-- products of the descendants.
#guard evalMle (contractPow 2 eight) r =
  ∑ x : Fin (2 ^ 1), (lagrangeBasis r)[x] * ∏ c : Fin 4, evalMle eight (childPoint 2 c (boolVec x))
-- With the descendants' bits in the high coordinates instead, the identity fails.
#guard evalMle (contractPow 2 eight) r ≠
  ∑ x : Fin (2 ^ 1), (lagrangeBasis r)[x] * ∏ c : Fin 4,
    evalMle eight ((boolVec x : Vector ℤ 1) ++ (boolVec c : Vector ℤ 2))

/-! ## Partial sums -/

/-- A function of two coordinates. -/
def g (v : Vector ℤ 2) : ℤ := v[0] * 10 + v[1] + 100

/-- The eq point. -/
def rr : Vector ℤ 2 := #v[3, 5]

-- Nothing fixed: the extension of the table of `g` at `rr`.
#guard partialSum g rr 0 #v[] = evalMle (Vector.ofFn fun x ↦ g (boolVec x)) rr
#guard partialSum g rr 0 #v[] =
  (1 - 3) * (1 - 5) * 100 + 3 * (1 - 5) * 110 + (1 - 3) * 5 * 101 + 3 * 5 * 111
-- One coordinate fixed: the split by `1 - r_0` and `r_0`.
#guard partialSum g rr 0 #v[] = (1 - 3) * partialSum g rr 1 #v[0] + 3 * partialSum g rr 1 #v[1]
#guard partialSum g rr 1 #v[7] = (1 - 5) * g #v[7, 0] + 5 * g #v[7, 1]
-- Everything fixed: the value.
#guard partialSum g rr 2 #v[7, 8] = g #v[7, 8]
-- Too much fixed: zero, by convention.
#guard partialSum g rr 3 #v[7, 8, 9] = 0

end LeanVMTests.Protocol.ProductTree
