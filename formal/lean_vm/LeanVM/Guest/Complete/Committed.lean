module

public import LeanVM.Guest.Budget.Runs
public import LeanVM.Guest.B1.Stack.Certify
public import LeanVM.Facts.Stack

/-!
# The committed size from the table rows

`Execution.committedSize` is the stack's `52` blocks at their columns' log-sizes: the memory's two
columns at `2^κ`, `q_keccak` at `2^(h_keccak + 6)`, and the other blocks at their tables' heights,
`7, 9, 5, 10, 14, 4` of them (`committedSize_eq`, the blocks' sources decided by the kernel). A
table's height `2^max(⌈log₂ rows⌉, floor)` is at most `2 rows + 2^floor` (`two_pow_height_le`), so
the committed size is at most `2^(κ+1) + 2 · tableWeighted t + 2^16`
(`committedOfRows : Budget.CommittedOfRows`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Guest.B1.Stack LeanVM.Node

@[expose] public section

/-- The blocks' kappa sources and adjustments, read off `colSrc`. -/
def blockSrcs : List (ℕ × ℕ) :=
  [(1, 0), (1, 0), (7, 6), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (3, 0), (3, 0),
    (3, 0), (3, 0), (3, 0), (3, 0), (3, 0), (3, 0), (3, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0),
    (5, 0), (5, 0), (5, 0), (5, 0), (5, 0), (5, 0), (5, 0), (5, 0), (5, 0), (5, 0), (6, 0), (6, 0),
    (6, 0), (6, 0), (6, 0), (6, 0), (6, 0), (6, 0), (6, 0), (6, 0), (6, 0), (6, 0), (6, 0), (6, 0),
    (7, 0), (7, 0), (7, 0), (7, 0)]

set_option maxRecDepth 100000 in
theorem blockSrcs_eq : stackBlocks.map (fun b ↦ colSrc.getD b.column (0, 0)) = blockSrcs := by
  decide +kernel

/-- The blocks' sizes summed, source by source. -/
theorem blockSrcs_sum (lm : ℕ) (hs : List ℕ) :
    (blockSrcs.map fun p ↦ 2 ^ (kvOf lm hs p.1 + p.2)).sum =
      2 * 2 ^ lm + 7 * 2 ^ hs.getD 0 0 + 9 * 2 ^ hs.getD 1 0 + 5 * 2 ^ hs.getD 2 0 +
        10 * 2 ^ hs.getD 3 0 + 14 * 2 ^ hs.getD 4 0 + (64 + 4) * 2 ^ hs.getD 5 0 := by
  simp (config := { decide := true }) only [blockSrcs, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, kvOf, ite_false, ite_true, Nat.add_zero]
  simp only [show (2 : ℕ) - 2 = 0 by rfl, show (3 : ℕ) - 2 = 1 by rfl, show (4 : ℕ) - 2 = 2 by rfl,
    show (5 : ℕ) - 2 = 3 by rfl, show (6 : ℕ) - 2 = 4 by rfl, show (7 : ℕ) - 2 = 5 by rfl, pow_add]
  ring

/-- A column's kappa is its source's plus its adjustment, `0` past the columns. -/
theorem kappa_getD (lm : ℕ) (hs : List ℕ) (c : ℕ) :
    (columnKappas tables lm hs).getD c 0 = kvOf lm hs (colSrc.getD c (0, 0)).1 +
      (colSrc.getD c (0, 0)).2 := by
  rw [columnKappas_eq]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases colSrc[c]? <;> simp [kvOf]

/-- **The committed size, block by block**, at the memory's log-size `lm` and the heights `hs`. -/
theorem committedSize_eq_sum (lm : ℕ) (hs : List ℕ) :
    (stackBlocks.map fun b ↦ 2 ^ (columnKappas tables lm hs).getD b.column 0).sum =
      2 * 2 ^ lm + 7 * 2 ^ hs.getD 0 0 + 9 * 2 ^ hs.getD 1 0 + 5 * 2 ^ hs.getD 2 0 +
        10 * 2 ^ hs.getD 3 0 + 14 * 2 ^ hs.getD 4 0 + (64 + 4) * 2 ^ hs.getD 5 0 := by
  have e : (stackBlocks.map fun b ↦ 2 ^ (columnKappas tables lm hs).getD b.column 0) =
      (stackBlocks.map fun b ↦ colSrc.getD b.column (0, 0)).map
        (fun p ↦ 2 ^ (kvOf lm hs p.1 + p.2)) := by
    rw [List.map_map]
    exact List.map_congr_left fun b _ ↦ by simp only [Function.comp, kappa_getD]
  rw [e, blockSrcs_eq]
  exact blockSrcs_sum lm hs

/-- A table's height is at most twice its rows plus its floor's. -/
theorem two_pow_height_le (r f : ℕ) : 2 ^ max (log2Ceil r) f ≤ 2 * r + 2 ^ f := by
  rcases le_total (log2Ceil r) f with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]
    unfold log2Ceil bitLength
    split_ifs with h0
    · have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
    · have h1 := Nat.log2_self_le (n := r - 1) h0
      generalize hx : 2 ^ Nat.log2 (r - 1) = x at h1
      rw [pow_succ, hx]
      generalize 2 ^ f = y
      omega

/-- **The committed size from the rows**: `Budget.CommittedOfRows`. -/
theorem committedOfRows : Budget.CommittedOfRows := by
  intro t
  have he := committedSize_eq_sum t.logMemorySize t.tableLogHeights
  simp only [Execution.committedSize]
  rw [he]
  simp only [Execution.tableLogHeights, Execution.tableRows, Budget.tableWeighted, tableLogFloors,
    List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_right, List.getD_cons_zero,
    List.getD_cons_succ, List.sum_cons, List.sum_nil]
  have h0 := two_pow_height_le (t.opcodeCount .xor) 0
  have h1 := two_pow_height_le (t.opcodeCount .mulNative) 0
  have h2 := two_pow_height_le (t.opcodeCount .setConstant) 0
  have h3 := two_pow_height_le (t.opcodeCount .deref) 0
  have h4 := two_pow_height_le (t.opcodeCount .jump) 0
  have h5 := two_pow_height_le (t.opcodeCount .keccak) keccakMinStepsLog
  have hk : keccakMinStepsLog = 9 := rfl
  rw [hk] at h5 ⊢
  rw [pow_succ]
  generalize 2 ^ max (log2Ceil (t.opcodeCount .xor)) 0 = a at *
  generalize 2 ^ max (log2Ceil (t.opcodeCount .mulNative)) 0 = b at *
  generalize 2 ^ max (log2Ceil (t.opcodeCount .setConstant)) 0 = c at *
  generalize 2 ^ max (log2Ceil (t.opcodeCount .deref)) 0 = d at *
  generalize 2 ^ max (log2Ceil (t.opcodeCount .jump)) 0 = e at *
  generalize 2 ^ max (log2Ceil (t.opcodeCount .keccak)) 9 = f at *
  generalize 2 ^ t.logMemorySize = m at *
  norm_num at *
  omega

end

end LeanVM.Guest.Complete
