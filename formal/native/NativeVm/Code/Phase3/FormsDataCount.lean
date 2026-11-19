module

public import NativeVm.Code.Phase3.FormsDataDefs

/-!
# The count blocks as literal data

`countD`: every table's count blocks in table order, checked against the statement (`countD_eq`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier

/-- The count blocks. -/
def countD : List DBlk := [
  (0, [(0, [9], 1)]),
  (0, [(0, [10], 1)]),
  (0, [(0, [11], 1)]),
  (0, [(0, [12], 1)]),
  (1, [(0, [9], 1)]),
  (1, [(0, [10], 1)]),
  (1, [(0, [11], 1)]),
  (1, [(0, [12], 1)]),
  (2, [(0, [5], 1)]),
  (2, [(0, [6], 1)]),
  (3, [(0, [10], 1)]),
  (3, [(0, [11], 1)]),
  (3, [(0, [12], 1)]),
  (3, [(0, [13], 1)]),
  (4, [(0, [8], 1)]),
  (4, [(0, [9], 1)]),
  (4, [(0, [10], 1)]),
  (4, [(0, [11], 1)]),
  (5, [(0, [65], 1)]),
  (5, [(0, [66], 1)]),
  (5, [(0, [67], 1)]),
  (5, [(0, [68], 1)]),
  (5, [(0, [69], 1)]),
  (5, [(0, [70], 1)]),
  (5, [(0, [71], 1)]),
  (5, [(0, [72], 1)]),
  (5, [(0, [73], 1)]),
  (5, [(0, [74], 1)]),
  (5, [(0, [75], 1)]),
  (5, [(0, [76], 1)]),
  (5, [(0, [77], 1)]),
  (5, [(0, [78], 1)]),
  (5, [(0, [79], 1)]),
  (5, [(0, [80], 1)]),
  (5, [(0, [81], 1)]),
  (5, [(0, [82], 1)]),
  (5, [(0, [83], 1)]),
  (5, [(0, [84], 1)]),
  (5, [(0, [85], 1)]),
  (5, [(0, [86], 1)]),
  (5, [(0, [87], 1)]),
  (5, [(0, [88], 1)]),
  (5, [(0, [89], 1)]),
  (5, [(0, [90], 1)]),
  (5, [(0, [91], 1)])]

/-- Each table's count columns. -/
def countCols : List (Nat × List Nat) :=
  [(0, [9, 10, 11, 12]), (1, [9, 10, 11, 12]), (2, [5, 6]), (3, [10, 11, 12, 13]),
    (4, [8, 9, 10, 11]), (5, (List.range 27).map (65 + ·))]

/-- The tables' count columns (by `simp`: the kernel does not evaluate `String.startsWith`). -/
theorem tables_countCols : tables.map (fun t ↦ (t.opcode, t.countColumns)) = countCols := by
  simp [Table.countColumns, tables, arithColumns, setColumns, derefColumns, jumpColumns,
    keccakColumns, laneNames, decimalNumeral, List.range_succ, countCols, opXor, opMul, opSet,
    opDeref, opJump, opKeccak]

/-- **The count blocks are the statement's.** -/
theorem countD_eq : countS = countD.map dprojW := by
  have h : countS = (tables.map (fun t ↦ (t.opcode, t.countColumns))).flatMap
      (fun p ↦ p.2.map fun l ↦ (p.1, entsS [Form.col l])) := by
    simp [countS, List.flatMap_map]
  rw [h, tables_countCols]
  decide +kernel

end NativeVm.Code.P3
