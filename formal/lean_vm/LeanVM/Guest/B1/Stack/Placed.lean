/-
  LeanVM.Guest.B1.Stack.Placed

  A stack block's placement in a layout `buildLayout` returns: its offset in closed form, aligned
  to its size, inside the stack.
-/

module

public import LeanVM.Guest.B1.Stack.Certify

/-!
# A block's placement

`layout_block`: in a layout `buildLayout` returns, stack block `b`'s column has a placement whose
`variableCount` is the block's kappa and whose `index` is the sum of `2^size` over the blocks before
it (`stackOffsets_closed`); the index is a multiple of `2^variableCount` (every block before it is
at least as large) and the block lies inside the stack (`index + 2^variableCount ≤ 2^stackLog`).
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Guest.Value

@[expose] public section

/-- Block `j`'s kappa in a layout. -/
def blockKap (layout : Layout) (j : ℕ) : ℕ :=
  (columnKappas tables layout.logMemory layout.tableLogHeights).getD (blockColumn j) 0

theorem stkBeforeSum_add_le (sz : ℕ → ℕ) {b : ℕ} (hb : b < 52) :
    stkBeforeSum sz 52 b + 2 ^ sz b ≤ ∑ j ∈ Finset.range 52, 2 ^ sz j := by
  unfold stkBeforeSum
  have hnot : b ∉ (Finset.range 52).filter (fun j ↦ StkBefore sz j b) := by
    rw [Finset.mem_filter]; simp [StkBefore]
  rw [add_comm, ← Finset.sum_insert (f := fun j ↦ 2 ^ sz j) hnot]
  exact Finset.sum_le_sum_of_subset (Finset.insert_subset (Finset.mem_range.2 hb) (Finset.filter_subset _ _))

theorem stkBeforeSum_dvd (sz : ℕ → ℕ) (b : ℕ) : 2 ^ sz b ∣ stkBeforeSum sz 52 b := by
  unfold stkBeforeSum
  refine Finset.dvd_sum fun j hj ↦ pow_dvd_pow 2 ?_
  have := (Finset.mem_filter.1 hj).2
  unfold StkBefore at this
  omega

/-- **Block `b`'s placement.** -/
theorem layout_block {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) {b : ℕ} (hb : b < 52) :
    ∃ p : Placement, layout.placements.getD (blockColumn b) none = some p ∧
      p.variableCount = blockKap layout b ∧ p.index = stkBeforeSum (blockKap layout) 52 b ∧
      2 ^ p.variableCount ∣ p.index ∧ p.index + 2 ^ p.variableCount ≤ 2 ^ layout.stackLog := by
  obtain ⟨hlm, -, -, -, -, hsl, hpl⟩ := buildLayout_some hbl
  rw [← hlm] at hsl hpl
  set kappas := columnKappas tables layout.logMemory layout.tableLogHeights with hkappas
  set sizes := stackBlocks.map fun bl ↦ kappas.getD bl.column 0 with hsizes
  have hszl : sizes.length = 52 := by simp [hsizes, stackBlocks_length]
  have hsz : ∀ j < 52, sizes.getD j 0 = blockKap layout j := fun j hj ↦ by
    simp [hsizes, blockKap, blockColumn, hkappas, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show j < stackBlocks.length by rw [stackBlocks_length]; exact hj)]
  obtain ⟨hoff, hlog⟩ := stackOffsets_closed sizes
  rw [hszl] at hoff hlog
  have hsum : stkBeforeSum (fun j ↦ sizes.getD j 0) 52 b = stkBeforeSum (blockKap layout) 52 b := by
    unfold stkBeforeSum
    rw [Finset.filter_congr fun x hx ↦ by
      simp only [StkBefore]; rw [hsz x (Finset.mem_range.1 hx), hsz b hb]]
    exact Finset.sum_congr rfl fun x hx ↦ by
      show 2 ^ sizes.getD x 0 = 2 ^ blockKap layout x
      rw [hsz x (Finset.mem_range.1 (Finset.mem_filter.1 hx).1)]
  obtain ⟨hcl, -⟩ := colSrc_block b hb
  have hkl : blockColumn b < kappas.length := by
    rw [hkappas, columnKappas_eq, List.length_map]; exact hcl
  have hlook : ((stackBlocks.map (·.column)).zip (stackOffsets sizes).1).lookup (blockColumn b) =
      some ((stackOffsets sizes).1.getD b 0) := by
    have := lookup_zip (stackBlocks.map (·.column)) (stackOffsets sizes).1 blockColumns_nodup
      (by rw [stackOffsets_length, List.length_map, hszl, stackBlocks_length]) b
      (by rw [List.length_map, stackBlocks_length]; exact hb)
    simpa [blockColumn, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show b < stackBlocks.length by rw [stackBlocks_length]; exact hb)] using this
  have htot : ∑ j ∈ Finset.range 52, 2 ^ blockKap layout j ≤ 2 ^ layout.stackLog := by
    rw [hsl, stack_eq, ← hsizes, hlog]
    have h1 : ∑ j ∈ Finset.range 52, 2 ^ blockKap layout j ≤
        2 ^ log2Ceil (∑ j ∈ Finset.range 52, 2 ^ sizes.getD j 0) := by
      rw [Finset.sum_congr rfl fun j hj ↦ by rw [← hsz j (Finset.mem_range.1 hj)]]
      exact log2Ceil_le_iff.mp le_rfl
    exact le_trans h1 (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  refine ⟨⟨kappas.getD (blockColumn b) 0, (stackOffsets sizes).1.getD b 0⟩, ?_, rfl, ?_, ?_, ?_⟩
  · rw [hpl, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
      List.getElem?_eq_getElem hkl]
    simp only [Option.map_some, Option.getD_some, Nat.zero_add, block_noSlot b hb]
    rw [stack_eq, ← hsizes, hlook]
    simp [List.getElem?_eq_getElem hkl]
  · show (stackOffsets sizes).1.getD b 0 = _
    rw [hoff b hb, hsum]
  · show 2 ^ blockKap layout b ∣ (stackOffsets sizes).1.getD b 0
    rw [hoff b hb, hsum]; exact stkBeforeSum_dvd _ b
  · show (stackOffsets sizes).1.getD b 0 + 2 ^ blockKap layout b ≤ _
    rw [hoff b hb, hsum]
    exact le_trans (stkBeforeSum_add_le _ hb) htot

end
end LeanVM.Guest.B1.Stack
