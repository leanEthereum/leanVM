import Rv64mc.Model.Walk

/-!
# Tests of the layout, bytecode, bus and walk mirrors

Executable checks on the Rust's own test vectors: `stack_offsets_place_largest_first_ties_by_index`
(`multilinear.rs`), the tables' widths and constraint counts (`layout.rs`), the counting sort, and
the smallest execution's stack against the statement's `placementsOf`.
-/

namespace Rv64mc.Model

open LeanVM.Protocol.Verifier

#guard (stackOffsetsRust [3, 5, 3, 0, 5, 1, 7, 1]).1.map BitVec.toNat ==
  [192, 128, 200, 212, 160, 208, 0, 210]
#guard (stackOffsetsRust [3, 5, 3, 0, 5, 1, 7, 1]).2 == 8
#guard (stackOffsetsRust [2, 2, 2]).1.map BitVec.toNat == [0, 4, 8]
#guard tablesRust.map TableRust.width == [13, 13, 7, 14, 14, 92]
#guard tablesRust.map TableRust.nConstraints == [0, 0, 0, 0, 2, 0]
#guard countingSortRust [(3, 0), (1, 1), (2, 2), (1, 3)] 4 Prod.fst ==
  [(1, 1), (1, 3), (2, 2), (3, 0)]
#guard (List.range 92).map qkeccakSlotRust == (List.range 92).map keccakSlot
#guard (List.range 300).map qkeccakSlotRust == (List.range 300).map keccakSlot
#guard minExecutionStackedLogRust 4 == (placementsOf (columnKappas 1 4 tableLogFloors)).2
#guard tagRust.map BitVec.toNat == [0x6c, 0x65, 0x61, 0x6e, 0x76, 0x6d, 0x2d, 0x76, 0x31]

/-- A one-instruction program: an `XOR` with operands `1, 2, 3`, its slots `n = 1` apart. -/
def xorProgram : List (BitVec 64) := [0, 0, 0, 1, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0]

#guard validEncodingRust xorProgram
#guard !validEncodingRust (xorProgram.set 3 3)
#guard !validEncodingRust (xorProgram.take 15)
#guard (newRust xorProgram).isSome
#guard (newRust xorProgram).map (·.blocks.map (·.map fun m ↦ (m.1.toNat, m.2.map BitVec.toNat))) ==
  some [[(2, [5]), (3, [6]), (1, [3, 4])]]

end Rv64mc.Model
