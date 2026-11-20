import Rv64mc.Model.Walk

/-!
# Tests of the layout, bytecode, bus and walk mirrors

Executable checks on the Rust's own test vectors: `stack_offsets_place_largest_first_ties_by_index`
(`multilinear.rs`), the tables' widths and constraint counts (`layout.rs`), the counting sort, and
the smallest execution's stack against the statement's `placementsOf`.
-/

namespace Rv64mc.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier

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


/-! ## Forms, the bus, `build_layout` and `evaluate` -/

/-- `add_scaled` merges a monomial already present and inserts a new one in order. -/
def mergedForm : Form :=
  addScaledRust ⟨[([1], eOfNat 2), ([3], eOfNat 4)]⟩ ⟨[([3], eOfNat 8), ([2], eOfNat 16)]⟩ 1

#guard mergedForm.terms.map (·.1) == [[1], [2], [3]]
#guard mergedForm.terms.map (·.2) == [eOfNat 2, eOfNat 16, eOfNat 4 + eOfNat 8]

#guard (List.range 40).all fun mu ↦ busGrindingBitsRust mu == busGrindingBits mu

/-- `build_layout` on the one-instruction program and memory `2^5`, in the Rust and the
statement. -/
def layoutPair (rows : List ℕ) : Option (LayoutRust × Layout) := do
  let l ← buildLayoutRust xorProgram.length 5#64 (rows.map (BitVec.ofNat 64))
  let L ← buildLayout (xorProgram.map BF64.ofBitVec) 5 rows
  pure (l, L)

/-- The blocks' sizes and owners. -/
def blockShape (bs : List BusBlock) : List (ℕ × ℕ × ℕ) :=
  bs.map fun b ↦ (b.logRows, b.rows, b.owner)

/-- The layouts agree, and so do their bus layouts. -/
def layoutAgrees (rows : List ℕ) : Bool :=
  match layoutPair rows with
  | some (l, L) =>
    let busRust := busLayoutRust [0, l.logMemory, l.logBytecode] l.push
    let bus := busLayout [0, L.logMemory, L.logBytecode] L.push
    l.logMemory == L.logMemory && l.logBytecode == L.logBytecode && l.stackLog == L.stackLog &&
      l.tableLogHeights == L.tableLogHeights &&
      l.placements.map (Option.map PlacementRust.toSpec) == L.placements &&
      blockShape (l.push ++ l.pull ++ l.count) == blockShape (L.push ++ L.pull ++ L.count) &&
      busRust.depth == bus.depth &&
      busRust.framework.map PlacementRust.toSpec == bus.framework &&
      busRust.tables.map PlacementRust.toSpec == bus.tables
  | none => false

#guard layoutAgrees [1, 0, 3, 700, 2, 1]
#guard layoutAgrees [0, 0, 0, 0, 0, 0]
#guard layoutAgrees [5000, 1, 1, 1, 1, 300]
#guard (buildLayoutRust 16 5#64 (List.replicate 6 (BitVec.ofNat 64 (2 ^ 30 + 1)))).isNone &&
  (buildLayout (xorProgram.map BF64.ofBitVec) 5 (List.replicate 6 (2 ^ 30 + 1))).isNone

/-- A point of the one-instruction program's four variables. -/
def xorPoint : List E := [eOfNat 3, eOfNat 5, eOfNat 7, eOfNat 11]

#guard ((newRust xorProgram).bind fun bc ↦ evaluateRust bc xorPoint) ==
  multilinearEvalRust (xorProgram.map wordE) xorPoint
#guard ((newRust xorProgram).bind fun bc ↦ evaluateRust bc (xorPoint.take 3)).isNone

end Rv64mc.Model
