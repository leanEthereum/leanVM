/-
  LeanVM.Protocol.EndToEnd.Front.BusStack

  The Python verifier's stacking of a list of blocks (`stack_offsets` and the placements of
  `bus_layout`) is the oracle protocol's stacking of the same blocks sorted largest first: the same
  order, the same offsets, and each placement's weight `eq_above` at a point is the protocol's
  selector weight of the block.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.LayoutStack
public import LeanVM.Protocol.ToCompPoly.AmbientStacking

/-!
# Stacking a list of blocks

A list `L` of blocks with log-sizes `κ`: the Python stacks the indices `0, …, n-1` by
`stack_offsets` (larger first, ties by index) and places block `i` at its offset; the protocol
sorts `L` largest first, stably (`sortedL`), and lays the blocks end to end (`blocksL`, the shape of
`Bus.blocks`). They are one layout:

* `sortedL_eq_map_ordL`: the sorted blocks are `L` read in the Python's order `ordL`;
* `stackOffsets_getD_ordL`: the Python's offset of the block at sorted position `b` is the
  protocol's offset of block `b`;
* `eqAbove_eq_selectorWeight`: the Python's `eq_above` of that placement at a point is the
  protocol's selector weight of block `b`;
* `sum_selectorWeight_eq`: a sum over the protocol's blocks of the selector weight times a quantity
  of the block is the sum over the Python's placements of `eq_above` times the quantity of the block
  at that index.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval

@[expose] public section

variable {α : Type} (L : List α) (κ : α → ℕ)

/-- The blocks sorted largest first, stably: `Bus.sorted`'s order. -/
def sortedL : List α := L.mergeSort fun a b ↦ decide (κ b ≤ κ a)

/-- The Python's order of the indices: `stack_offsets`' stable sort by size. -/
def ordL : List ℕ :=
  (List.range L.length).mergeSort fun i j ↦ decide ((L.map κ).getD j 0 ≤ (L.map κ).getD i 0)

theorem ordL_perm : (ordL L κ).Perm (List.range L.length) := List.mergeSort_perm _ _

theorem length_ordL : (ordL L κ).length = L.length := by
  rw [(ordL_perm L κ).length_eq, List.length_range]

theorem length_sortedL : (sortedL L κ).length = L.length := List.length_mergeSort _

theorem ordL_lt {i : ℕ} (hi : i ∈ ordL L κ) : i < L.length :=
  List.mem_range.mp ((ordL_perm L κ).mem_iff.mp hi)

/-- **The sorted blocks are `L` in the Python's order.** -/
theorem sortedL_eq_map_ordL (x₀ : α) : sortedL L κ = (ordL L κ).map fun i ↦ L.getD i x₀ := by
  rw [ordL, List.map_mergeSort (s := fun a b ↦ decide (κ b ≤ κ a))]
  · congr 1
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getElem?_eq_getElem h1]
  · intro a ha b hb
    rw [List.mem_range] at ha hb
    simp [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]

/-- The `b`-th sorted block. -/
theorem getElem_sortedL (x₀ : α) (b : ℕ) (hb : b < (sortedL L κ).length) :
    (sortedL L κ)[b] = L.getD ((ordL L κ)[b]'(by rw [length_ordL]; rwa [length_sortedL] at hb))
      x₀ := by
  simp only [sortedL_eq_map_ordL L κ x₀, List.getElem_map]

/-- **The Python's offsets are prefix sums in the sorted order.** -/
theorem stackOffsets_getD_ordL (x₀ : α) (b : ℕ) (hb : b < L.length) :
    (stackOffsets (L.map κ)).1.getD ((ordL L κ)[b]'(by rwa [length_ordL])) 0 =
      (((sortedL L κ).take b).map fun a ↦ 2 ^ κ a).sum := by
  have hnd : (ordL L κ).Nodup := (ordL_perm L κ).nodup_iff.mpr List.nodup_range
  rw [stackOffsets_eq]
  simp only [List.length_map]
  change ((ordL L κ).foldl (placeStep fun i ↦ 2 ^ (L.map κ).getD i 0)
    (List.replicate L.length 0, 0)).1.getD _ 0 = _
  have hfold := placeFold_getElem? (fun i ↦ 2 ^ (L.map κ).getD i 0) (ordL L κ) hnd
    (List.replicate L.length 0, 0) (fun i hi ↦ by simpa using ordL_lt L κ hi) b
    (by rwa [length_ordL])
  rw [List.getD_eq_getElem?_getD, hfold, Option.getD_some, zero_add,
    sortedL_eq_map_ordL L κ x₀, ← List.map_take, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
  have hi' := ordL_lt L κ (List.mem_of_mem_take hi)
  simp [List.getElem?_eq_getElem hi']

/-! ## The protocol's layout of the sorted blocks -/

/-- A layout of the sorted blocks: its offsets are prefix sums in the sorted order. -/
theorem offsetNat_sortedL (B : Blocks) (hn : B.n = (sortedL L κ).length)
    (hs : ∀ b : Fin B.n, B.size b = κ ((sortedL L κ)[b.val]'(hn ▸ b.isLt))) (k : ℕ)
    (hk : k ≤ B.n) : B.offsetNat k = (((sortedL L κ).take k).map fun a ↦ 2 ^ κ a).sum := by
  induction k with
  | zero => simp [Blocks.offsetNat]
  | succ k ih =>
    rw [Blocks.offsetNat_succ _ k (by omega), ih (by omega),
      List.take_succ_eq_append_getElem (by omega), List.map_append, List.sum_append, hs]
    simp

/-! ## Placements and selector weights -/

/-- The Python's placements of the blocks of sizes `sizes` (`bus_layout`). -/
def pyPlacements (sizes : List ℕ) : List Placement :=
  List.zipWith (fun size offset ↦ ({ vars := size, index := offset } : Placement)) sizes
    (stackOffsets sizes).1

theorem length_stackOffsets_fst (sizes : List ℕ) :
    (stackOffsets sizes).1.length = sizes.length := by
  rw [stackOffsets_eq]
  simp only
  rw [placeFold_length, List.length_replicate]

theorem length_pyPlacements (sizes : List ℕ) : (pyPlacements sizes).length = sizes.length := by
  simp [pyPlacements, length_stackOffsets_fst]

/-- The placement of the block at sorted position `b`. -/
theorem pyPlacements_getElem_ordL (x₀ : α) (b : ℕ) (hb : b < L.length) :
    (pyPlacements (L.map κ))[(ordL L κ)[b]'(by rwa [length_ordL])]'(by
        rw [length_pyPlacements, List.length_map]
        exact ordL_lt L κ (List.getElem_mem _)) =
      { vars := κ ((sortedL L κ)[b]'(by rwa [length_sortedL])),
        index := (((sortedL L κ).take b).map fun a ↦ 2 ^ κ a).sum } := by
  have hi := ordL_lt L κ (List.getElem_mem (l := ordL L κ) (n := b) (by rwa [length_ordL]))
  simp only [pyPlacements, List.getElem_zipWith, List.getElem_map]
  rw [← stackOffsets_getD_ordL L κ x₀ b hb, List.getD_eq_getElem _ _ (by
    rw [length_stackOffsets_fst, List.length_map]; exact hi), getElem_sortedL L κ x₀,
    List.getD_eq_getElem _ _ hi]

/-- `eq_eval` is symmetric. -/
theorem eqEval_comm (a b : List E) : eqEval a b = eqEval b a := by
  rw [eqEval_eq_list_prod, eqEval_eq_list_prod, List.zipWith_comm]
  have hf : (fun x y : E ↦ 1 + y + x) = fun x y ↦ 1 + x + y := by
    funext x y; ring
  rw [hf]

/-- The high coordinates of a point, as a list, are the point's list past the low ones. -/
theorem toList_highPoint (B : Blocks) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (z : Vector E μ) : (B.highPoint hμ b z).toList = z.toList.drop (B.size b) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [Blocks.highPoint, highVec]

/-- **`eq_above` is the selector weight**: the Python's weight of a block placed at the protocol's
offset, at a point, is the protocol's selector weight of the block there. -/
theorem eqAbove_eq_selectorWeight (B : Blocks) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (z : Vector E μ) :
    ({ vars := B.size b, index := B.offset b } : Placement).eqAbove z.toList =
      B.selectorWeight hμ b z := by
  rw [Blocks.selectorWeight]
  have h := eqEval_boolPoint (B.highPoint hμ b z) (B.selector hμ b)
  rw [← h, toList_highPoint, eqEval_comm, Blocks.selector_val]
  simp only [Placement.eqAbove, zero_add, Vector.length_toList, Nat.sub_zero,
    selectorPoint_eq_boolPoint, Nat.shiftRight_eq_div_pow]

/-! ## Sums over the blocks -/

/-- The Python's order as a bijection of the sorted positions onto the indices. -/
theorem ordL_bijective (hn : (ordL L κ).length = L.length) :
    Function.Bijective fun b : Fin L.length ↦
      (⟨(ordL L κ)[b.val]'(by rw [hn]; exact b.isLt),
        ordL_lt L κ (List.getElem_mem _)⟩ : Fin L.length) := by
  have hnd : (ordL L κ).Nodup := (ordL_perm L κ).nodup_iff.mpr List.nodup_range
  constructor
  · intro a b hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext ((hnd.getElem_inj_iff).mp hab)
  · intro i
    have hi : i.val ∈ ordL L κ := (ordL_perm L κ).mem_iff.mpr (List.mem_range.mpr i.isLt)
    obtain ⟨b, hb, hbi⟩ := List.mem_iff_getElem.mp hi
    exact ⟨⟨b, by rwa [← hn]⟩, Fin.ext hbi⟩

/-- **A sum over the protocol's blocks is a sum over the Python's placements**: the selector
weight of block `b` times a quantity of the `b`-th sorted block, summed over the blocks, is
`eq_above` of placement `i` times the quantity of block `i` of `L`, summed over the indices. -/
theorem sum_selectorWeight_eq (x₀ : α) (B : Blocks) (hn : B.n = (sortedL L κ).length)
    (hs : ∀ b : Fin B.n, B.size b = κ ((sortedL L κ)[b.val]'(hn ▸ b.isLt))) {μ : ℕ}
    (hμ : B.total ≤ 2 ^ μ) (z : Vector E μ) (F : α → E) :
    ∑ b : Fin B.n, B.selectorWeight hμ b z * F ((sortedL L κ)[b.val]'(hn ▸ b.isLt)) =
      ∑ i : Fin L.length, ((pyPlacements (L.map κ))[i.val]'(by
        rw [length_pyPlacements, List.length_map]; exact i.isLt)).eqAbove z.toList * F L[i] := by
  have hn' : B.n = L.length := by rw [hn, length_sortedL]
  rw [← (Equiv.ofBijective _ (ordL_bijective L κ (length_ordL L κ))).sum_comp]
  rw [← (finCongr hn').sum_comp]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp only [Equiv.ofBijective_apply, finCongr_apply, Fin.val_cast]
  have hb : b.val < L.length := by rw [← hn']; exact b.isLt
  congr 1
  · rw [pyPlacements_getElem_ordL L κ x₀ b hb, ← eqAbove_eq_selectorWeight B hμ b z, hs b,
      Blocks.offset, offsetNat_sortedL L κ B hn hs b b.isLt.le]
  · rw [getElem_sortedL L κ x₀, List.getD_eq_getElem _ _ (ordL_lt L κ (List.getElem_mem _))]
    rfl

end
end LeanVM.Protocol.EndToEnd.Front
