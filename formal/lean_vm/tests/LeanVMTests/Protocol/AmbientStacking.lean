/-
  LeanVMTests.Protocol.AmbientStacking

  Regression controls for empty, full, and padded ambient stack evaluation.
-/

module

public import LeanVM.Protocol.ToCompPoly.AmbientStacking
public import LeanVMTests.Protocol.Stacking
meta import LeanVM.Protocol.ToCompPoly.AmbientStacking
meta import LeanVMTests.Protocol.Stacking

/-!
# Ambient padding controls

An empty layout evaluates to its pad, a full layout has weights summing to one and a layout
with a gap does not, and the decomposition is evaluated on both sides at a point of the larger
field, with the pad term dropped as the mutation.
-/

namespace LeanVMTests.Protocol

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

/-! ## The empty layout -/

example (z : Vector K 2) : evalMle (emptyBlocks.stackAt emptyTables 2 1) z = 1 := by
  have ht : emptyBlocks.stackAt emptyTables 2 1 = Vector.replicate (2 ^ 2) (1: K) := by
    apply Vector.ext
    intro i hi
    rw [emptyBlocks.stackAt_getElem_of_total_le emptyTables 1 hi (by
      have he : emptyBlocks.total = 0 := by decide
      rw [he]
      exact Nat.zero_le i)]
    simp only [Vector.getElem_replicate]
  rw [ht]
  exact evalMle_replicate 1 z

#guard evalMle (emptyBlocks.stackAt emptyTables 2 1) (#v[K.ofBits 5, K.ofBits 9] : Vector K 2) = 1

/-! ## Weights of a full layout and of a layout with a gap -/

/-- Blocks on 1, 0 and 0 variables: heights 2, 1, 1, which fill a stack of height 4. -/
def fullBlocks : Blocks where
  n := 3
  size := ![1, 0, 0]
  descending := by
    show ∀ a b : Fin 3, a ≤ b → ![1, 0, 0] b ≤ ![1, 0, 0] a
    decide

theorem fullBlocks_total : fullBlocks.total = 2 ^ 2 := by decide

example (z : Vector K 2) :
    (∑ b : Fin fullBlocks.n, fullBlocks.selectorWeight fullBlocks_total.le b z) = 1 :=
  fullBlocks.sum_selectorWeight_of_total_eq fullBlocks_total z

-- The weights of the full layout sum to one off the cube.
#guard (∑ b : Fin fullBlocks.n,
  fullBlocks.selectorWeight fullBlocks_total.le b (#v[K.ofBits 5, K.ofBits 9] : Vector K 2)) = 1
-- Those of the fixture, which leaves one cell uncovered, do not.
#guard (∑ b : Fin blocks.n,
  blocks.selectorWeight blocks_total_le b (#v[K.ofBits 5, K.ofBits 9, K.ofBits 11] : Vector K 3)) ≠ 1
-- At a lifted point of a block, that block's weight is one.
#guard blocks.selectorWeight blocks_total_le (1 : Fin 3)
  (blocks.extendPoint blocks_total_le (1 : Fin 3) (#v[K.ofBits 13] : Vector K 1)) = 1

/-! ## The decomposition, evaluated -/

/-- A point of `E^3` off the cube and outside `K`. -/
def offCube : Vector E 3 := #v[E.ofLimbs 0 1 0, E.ofLimbs 1 1 0, E.ofLimbs 0 0 1]

/-- The blocks' share of the stack at `offCube`. -/
def coveredPart : E :=
  ∑ b : Fin blocks.n, blocks.selectorWeight blocks_total_le b offCube *
    eval₂Mle (tables b) (algebraMap K E) (blocks.lowPoint blocks_total_le b offCube)

/-- The weight no block covers at `offCube`. -/
def uncoveredWeight : E :=
  1 - ∑ b : Fin blocks.n, blocks.selectorWeight blocks_total_le b offCube

-- Pad 5: the blocks' share plus five times the uncovered weight.
#guard eval₂Mle (blocks.stackAt tables 3 (K.ofBits 5)) (algebraMap K E) offCube =
  coveredPart + ofK (K.ofBits 5) * uncoveredWeight
-- Pad 0: the blocks' share alone.
#guard eval₂Mle (blocks.stackAt tables 3 0) (algebraMap K E) offCube = coveredPart
-- Mutation: with a nonzero pad, dropping the pad term is wrong.
#guard eval₂Mle (blocks.stackAt tables 3 (K.ofBits 5)) (algebraMap K E) offCube ≠ coveredPart
#guard eval₂Mle (blocks.stackAt tables 3 1) (algebraMap K E) offCube ≠
  eval₂Mle (blocks.stackAt tables 3 0) (algebraMap K E) offCube

end
end LeanVMTests.Protocol
