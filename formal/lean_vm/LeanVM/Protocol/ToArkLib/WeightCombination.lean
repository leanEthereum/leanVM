/-
  LeanVM.Protocol.ToArkLib.WeightCombination

  A linear combination of weights of the inner-product interface, and the answer to it.
  Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.InnerProduct
public import LeanVM.Protocol.ToCompPoly.Multilinear

/-!
# Combined weights

`Weight.combine ts` combines the weights of the list `ts` with their coefficients: its values are
`Σ_{(c, W)} c · W(x)` and its extension, the one the asker evaluates, is `Σ_{(c, W)} c · W̃(r)`,
from the weights' own evaluators. The answer of a table to the combination is the combination of
its answers (`Weight.pair_combine`): the inner product is linear in the weight.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The weights of `ts` combined with their coefficients. -/
def Weight.combine {n : ℕ} (ts : List (S × Weight S n)) : Weight S n where
  onCube := Vector.ofFn fun x ↦ (ts.map fun t ↦ t.1 * t.2.onCube[x]).sum
  mle := fun r ↦ (ts.map fun t ↦ t.1 * t.2.mle r).sum
  mle_eq := fun r ↦ by
    induction ts with
    | nil => simp [evalMle_eq_sum]
    | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons, ih, t.2.mle_eq, evalMle_eq_sum, Fin.getElem_fin,
        Vector.getElem_ofFn, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- The answer of a table to combined weights is the combination of its answers. -/
theorem Weight.pair_combine {n : ℕ} (φ : R →+* S) (ts : List (S × Weight S n))
    (t : CMlPolynomialEval R n) :
    (Weight.combine ts).pair φ t = (ts.map fun w ↦ w.1 * w.2.pair φ t).sum := by
  induction ts with
  | nil => simp [Weight.pair, Weight.combine]
  | cons w ts ih =>
    simp only [List.map_cons, List.sum_cons, ← ih]
    simp only [Weight.pair, Weight.combine, Fin.getElem_fin, Vector.getElem_ofFn, List.map_cons,
      List.sum_cons, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

end
end LeanVM.Protocol
