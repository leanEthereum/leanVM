import LeanVM.Protocol.EndToEnd.Front.BusStack
import LeanVM.Protocol.EndToEnd.Complete.BusSide

/-!
# Tests: stacked blocks and forms

* **The verifier's order is the protocol's.** For block sizes with ties, `stack_offsets`' order
  (`ordL`) reads the blocks largest first, ties by index, which is the protocol's stable sort
  (`sortedL`); the verifier's offsets are the prefix sums in that order.
* **Mutation.** Breaking ties by the higher index gives another order: the stability of both sorts
  is what makes the two layouts one.
* **Forms are linear.** `add_scaled` adds the scaled value, also when the added form repeats a
  monomial (merged into one coefficient), and the leaf accumulation adds a block's value to its
  owner's form on the accumulated side only.
-/

namespace LeanVMTests.Protocol.EndToEnd.Front.Stack

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete

/-- Blocks named by their index, with ties among the sizes. -/
def sizes : List ℕ := [1, 3, 0, 3, 2, 1]

/-- The block's own size. -/
def κ (i : ℕ) : ℕ := sizes.getD i 0

/-- The blocks, as their indices. -/
def blocks : List ℕ := List.range sizes.length

#guard ordL blocks κ == [1, 3, 4, 0, 5, 2]
#guard sortedL blocks κ == [1, 3, 4, 0, 5, 2]

-- The verifier's offsets at the sorted positions are the prefix sums of the sorted sizes.
#guard (List.range blocks.length).map (fun b ↦
    (stackOffsets (blocks.map κ)).1.getD ((ordL blocks κ).getD b 0) 0) ==
    (List.range blocks.length).map fun b ↦
      (((sortedL blocks κ).take b).map fun a ↦ 2 ^ κ a).sum

-- Mutation: ties broken by the higher index give another order.
#guard ((List.range sizes.length).mergeSort fun i j ↦
    decide (sizes.getD j 0 < sizes.getD i 0 ∨ (sizes.getD j 0 = sizes.getD i 0 ∧ j ≤ i))) !=
      sortedL blocks κ

/-! ## Forms -/

/-- A form with a repeated monomial. -/
def f₁ : Form := ⟨[([0, 1], 3), ([2], 5)]⟩

/-- A form sharing a monomial with `f₁`. -/
def f₂ : Form := ⟨[([2], 7), ([1, 1], 1), ([], 2)]⟩

/-- A row of columns. -/
def col (i : ℕ) : E := (i + 2 : ℕ)

#guard (f₁.addScaled f₂ 11).evaluate col == f₁.evaluate col + 11 * f₂.evaluate col
#guard (f₁.addScaled f₂ 11).terms.length == 4

example (w : E) : (f₁.addScaled f₂ w).evaluate col = f₁.evaluate col + w * f₂.evaluate col :=
  evaluate_addScaled f₁ f₂ w col

/-- A block owned by table `1`, two coordinates, three of its four rows flushing. -/
def blk : BusBlock := ⟨2, 3, [Form.col 0, Form.col 1 3], 1⟩

/-- Three tables of two sides of empty forms. -/
def forms₀ : List (List Form) := List.replicate 3 (List.replicate 2 {})

/-- The value of the form of table `t` and side `k`. -/
def formVal (forms : List (List Form)) (t k : ℕ) : E := ((forms.getD t []).getD k {}).evaluate col

#guard formVal (accFold 1 [5, 7] 9 [(4, blk)] forms₀) 1 1 == 4 * blockVal 9 [5, 7] blk col
#guard formVal (accFold 1 [5, 7] 9 [(4, blk)] forms₀) 1 0 == 0
#guard formVal (accFold 1 [5, 7] 9 [(4, blk)] forms₀) 0 1 == 0

end LeanVMTests.Protocol.EndToEnd.Front.Stack
