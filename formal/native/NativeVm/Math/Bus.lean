module

public import NativeVm.Model.Layout

/-!
# The count side of the bus
-/

@[expose] public section

namespace NativeVm.Math.Bus

open NativeVm.Model LeanVM.Protocol.Verifier

def shapeC : List (Nat × Nat) := [(0, 4), (1, 4), (2, 2), (3, 4), (4, 4), (5, 27)]

theorem tables_count : tables.map (fun t ↦ (t.opcode, t.countColumns.length)) = shapeC := by
  simp [Table.countColumns, tables, arithColumns, setColumns, derefColumns, jumpColumns,
    keccakColumns, laneNames, decimalNumeral, List.range_succ, shapeC, opXor, opMul, opSet,
    opDeref, opJump, opKeccak]

end NativeVm.Math.Bus
