import Whir.AnchorPrefixRefinement

/-! The shared Rows arithmetic expression adapter reaches the same occupied-prefix dense claim as Native. This theorem does not assert a physical circuit-row-count bound or a separate compiler correctness theorem. -/
namespace Whir.AnchorPrefixRefinementRows
open Concrete Protocol AnchoredHeaderCodec AnchorPrefixRefinementArith

/-- The Rows entry point is just the shared source algorithm on arithmetic expressions. -/
def rowsAnchorAt (shape : Shape) (r x : Array RowsExpr) : RowsExpr :=
  anchorAtWith rows shape r.size (fun j => r[j]!) (fun j => x[j]!)

lemma eval_map_bang (a : Array RowsExpr) (j : Nat) :
    (a.map RowsExpr.eval)[j]! = (a[j]!).eval := by
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.map RowsExpr.eval) j (by simpa using hj),
      getElem!_pos a j hj, Array.getElem_map]
  · rw [getElem!_neg (a.map RowsExpr.eval) j (by simpa using hj), getElem!_neg a j hj]
    rfl

/-- Operational Native/Rows adapter, with primitive expression semantics proved rather than a final correct-weight premise. -/
theorem rowsAnchorAt_native (shape : Shape) (r x : Array RowsExpr) :
    (rowsAnchorAt shape r x).eval =
      AnchoredPhysicalAnchor.anchorAt shape (r.map RowsExpr.eval) (x.map RowsExpr.eval) := by
  rw [rowsAnchorAt, native_rows_anchor]
  unfold AnchoredPhysicalAnchor.anchorAt
  simp only [Array.size_map]
  congr 1 <;> funext j <;> simp [Function.comp_apply, eval_map_bang]

/-- Full-cube and arbitrary occupied-prefix Rows arithmetic reach the actual dense anchor encoding. -/
theorem rowsAnchorAt_dense (c : Config) (shape : Shape) (r x : Array RowsExpr)
    (hN : shape.logN = c.logN) (hB : shape.logBatch = c.folds[0]!)
    (occupied : 0 < shape.lanes ∧ shape.lanes ≤ 2^shape.logBatch)
    (dimensions : shape.logBatch < shape.logN)
    (hr : r.size = shape.logN) (hx : x.size = shape.logN) :
    (rowsAnchorAt shape r x).eval =
      Concrete.mle (CommitmentAnchor.weight c shape.lanes (r.map RowsExpr.eval)) (x.map RowsExpr.eval) := by
  rw [rowsAnchorAt_native]
  exact AnchorPrefixRefinement.anchorAt_dense c shape _ _ hN hB occupied dimensions
    (by simpa using hr) (by simpa using hx)

#print axioms rowsAnchorAt_native
#print axioms rowsAnchorAt_dense
end Whir.AnchorPrefixRefinementRows
