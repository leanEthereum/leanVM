module

public import LeanVM.Arithmetization.Bytecode
meta import LeanVM.Arithmetization.Bytecode

/-!
# Tests: the bytecode encoding

One instruction per constructor, `DEREF` in each of its three modes, laid out by `entry` and read
back by `decode` under compiled evaluation. The slot positions are
pinned against the table of specification §8.1 (`08-end-to-end-protocol.tex`):
`SET_CONSTANT`'s `k₁` at slot 6, slot 7 spare, and `KECCAK`'s ten operands at slots 4 to 13 (`o_{m₀..m₃}, o_tail,
o_b8, o_cap, o_out` and the two layout flags). The flag pairs and the opcode words are pinned
against `cpu/isa.rs` and `tables.rs` (leanVM `4af2cddd`).
The mutations at the end reject the flag pair `(1, 1)`, a non-Boolean flag (`DEREF`'s and
`KECCAK`'s), an unknown opcode, and a nonzero spare slot; the first is also derived from
`decode_eq_none_iff`, so the rejection is a theorem and not only an evaluation.

Vector equalities are stated on word lists (`Vector.toList`), because core's `DecidableEq` for
`Vector` is not exposed to module-system importers.
-/

namespace LeanVMTests.Arithmetization

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization

public section

/-! ## One instruction per constructor -/

def xorI : LeanIsaInstruction := .xor (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4)
def mulI : LeanIsaInstruction := .mulNative (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4)
def setI : LeanIsaInstruction := .setConstant (addressOfIndex 2) (E.ofLimbs (K.ofBits 7) (K.ofBits
    8))
def derefCellI : LeanIsaInstruction := .deref (addressOfIndex 4) 1 (addressOfIndex 5) .cell
def derefPcI : LeanIsaInstruction := .deref (addressOfIndex 4) 1 (addressOfIndex 5) .pc
def derefFpI : LeanIsaInstruction := .deref (addressOfIndex 4) 1 (addressOfIndex 5) .fp
def jumpI : LeanIsaInstruction := .jump (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4)
def keccakI : LeanIsaInstruction := .keccak ![addressOfIndex 6, addressOfIndex 7, addressOfIndex 6, addressOfIndex 7] (addressOfIndex 8) (addressOfIndex 12) (addressOfIndex 13) (addressOfIndex 17)
  false true .two

/-! ## The flags and the codes -/

-- `Cell = (0, 0)`, `Pc = (1, 0)`, `Fp = (0, 1)` (`isa.rs`).
#guard derefFlags .cell = (0, 0)
#guard derefFlags .pc = (1, 0)
#guard derefFlags .fp = (0, 1)
#guard derefMode? 0 0 = some .cell
#guard derefMode? 1 0 = some .pc
#guard derefMode? 0 1 = some .fp
#guard derefMode? 1 1 = none

-- The six codes are the words `1, 2, 4, 8, 16, 32`; `0x40` and `0` are no opcode.
#guard opcode? 0x01 = some .xor
#guard opcode? (K.ofBits 0x02) = some .mulNative
#guard opcode? (K.ofBits 0x04) = some .setConstant
#guard opcode? (K.ofBits 0x08) = some .deref
#guard opcode? (K.ofBits 0x10) = some .jump
#guard opcode? (K.ofBits 0x20) = some .keccak
#guard opcode? (K.ofBits 0x40) = none
#guard opcode? 0 = none

/-! ## Slots 3 to 15 (specification §8.1) -/

#guard (busEntry xorI).toList = [Opcode.xor.busCode, addressOfIndex 2, addressOfIndex 3,
    addressOfIndex 4, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (busEntry mulI).toList = [Opcode.mulNative.busCode, addressOfIndex 2, addressOfIndex 3,
    addressOfIndex 4, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (busEntry setI).toList =
  [Opcode.setConstant.busCode, addressOfIndex 2, K.ofBits 7, K.ofBits 8, 0, 0, 0, 0,
      0, 0, 0, 0, 0]
#guard (busEntry derefCellI).toList = [Opcode.deref.busCode, addressOfIndex 4, 1, addressOfIndex 5,
    0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (busEntry derefPcI).toList = [Opcode.deref.busCode, addressOfIndex 4, 1, addressOfIndex 5, 1,
    0, 0, 0, 0, 0, 0, 0, 0]
#guard (busEntry derefFpI).toList = [Opcode.deref.busCode, addressOfIndex 4, 1, addressOfIndex 5, 0,
    1, 0, 0, 0, 0, 0, 0, 0]
#guard (busEntry jumpI).toList = [Opcode.jump.busCode, addressOfIndex 2, addressOfIndex 3,
    addressOfIndex 4, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (busEntry keccakI).toList =
  [Opcode.keccak.busCode, addressOfIndex 6, addressOfIndex 7, addressOfIndex 6, addressOfIndex 7,
      addressOfIndex 8, addressOfIndex 12, addressOfIndex 13, addressOfIndex 17, 0, 1, 1, 0]

-- The sixteen slots: the opcode at 3, the operands at 4 to 15, zero at 0 to 2.
#guard (instructionSlots setI).toList =
  [0, 0, 0, Opcode.setConstant.busCode, addressOfIndex 2, K.ofBits 7, K.ofBits 8, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (instructionSlots keccakI).toList =
  [0, 0, 0, Opcode.keccak.busCode, addressOfIndex 6, addressOfIndex 7, addressOfIndex 6,
      addressOfIndex 7, addressOfIndex 8, addressOfIndex 12, addressOfIndex 13, addressOfIndex 17,
    0, 1, 1, 0]

/-- Slot 3 is the opcode, through `encodeSlots_getElem` and `entry_getElem_zero`. -/
example : (instructionSlots setI)[3] = Opcode.setConstant.busCode := by
  simp [encodeSlots_getElem, entry_getElem_zero, setI, LeanIsaInstruction.opcode]

/-- `k₁` rides slot 6 and slot 7 is a spare zero, checked in the kernel. -/
example : (instructionSlots setI)[6] = K.ofBits 8 ∧ (instructionSlots setI)[7] = 0 := by
  decide +kernel

/-! ## Round trips -/

#guard decode (busEntry xorI) = some xorI
#guard decode (busEntry mulI) = some mulI
#guard decode (busEntry setI) = some setI
#guard decode (busEntry derefCellI) = some derefCellI
#guard decode (busEntry derefPcI) = some derefPcI
#guard decode (busEntry derefFpI) = some derefFpI
#guard decode (busEntry jumpI) = some jumpI
#guard decode (busEntry keccakI) = some keccakI
#guard decode (busEntry (.keccak ![1, g, addressOfIndex 2, addressOfIndex 3] (addressOfIndex 4) (addressOfIndex 8) (addressOfIndex 9) (addressOfIndex 13) true false .all)) =
  some (.keccak ![1, g, addressOfIndex 2, addressOfIndex 3] (addressOfIndex 4) (addressOfIndex 8)
      (addressOfIndex 9) (addressOfIndex 13) true false .all)

/-- The literal entry of `SET_CONSTANT` decodes to it: `decode` is exact. -/
example : decode #v[Opcode.setConstant.busCode, addressOfIndex 2, K.ofBits 7, K.ofBits 8, 0, 0, 0, 0, 0, 0, 0, 0, 0] =
    some setI :=
  decode_eq_some_iff.mpr rfl

-- The `DEREF` modes are told apart by their entries.
#guard (busEntry derefPcI).toList ≠ (busEntry derefFpI).toList
example : derefPcI ≠ derefFpI := fun h ↦ by cases h

/-! ## Nearby false statements -/

-- The flag pair `(1, 1)` is not an instruction, nor is a non-Boolean flag.
#guard decode #v[Opcode.deref.busCode, addressOfIndex 4, 1, addressOfIndex 5, 1, 1, 0, 0, 0, 0,
    0, 0, 0] = none
#guard decode #v[Opcode.deref.busCode, addressOfIndex 4, 1, addressOfIndex 5, g, 0, 0, 0, 0, 0,
    0, 0, 0] = none
-- An unknown opcode is not an instruction.
#guard decode #v[addressOfIndex 6, addressOfIndex 2, addressOfIndex 3, addressOfIndex 4, 0, 0, 0, 0,
    0, 0, 0, 0, 0] = none
#guard decode #v[0, addressOfIndex 2, addressOfIndex 3, addressOfIndex 4, 0, 0, 0, 0, 0, 0,
    0, 0, 0] = none
-- A nonzero spare entry coordinate is outside the canonical typed-program encoding.
#guard decode #v[Opcode.xor.busCode, addressOfIndex 2, addressOfIndex 3, addressOfIndex 4, 1, 0, 0,
    0, 0, 0, 0, 0, 0] = none
#guard decode #v[Opcode.setConstant.busCode, addressOfIndex 2, K.ofBits 7, K.ofBits 8, 1, 0, 0, 0, 0, 0, 0, 0, 0] = none
#guard decode #v[Opcode.setConstant.busCode, addressOfIndex 2, K.ofBits 7, K.ofBits 8, 0, 1, 0, 0, 0, 0, 0, 0, 0] = none
#guard decode #v[Opcode.deref.busCode, addressOfIndex 4, 1, addressOfIndex 5, 1, 0, 0, 1, 0, 0,
    0, 0, 0] = none
#guard decode #v[Opcode.jump.busCode, addressOfIndex 2, addressOfIndex 3, addressOfIndex 4, 0, 0, 0,
    1, 0, 0, 0, 0, 0] = none
#guard decode #v[Opcode.jump.busCode, addressOfIndex 2, addressOfIndex 3, addressOfIndex 4, 0, 0, 0,
    0, 0, 0, 1, 0, 0] = none
-- A `KECCAK` layout flag must be `0` or `1`.
#guard decode #v[Opcode.keccak.busCode, addressOfIndex 6, addressOfIndex 7, addressOfIndex 6, addressOfIndex 7, addressOfIndex 8, addressOfIndex 12, addressOfIndex 13, addressOfIndex 17,
  g, 1, 1, 0] = none
#guard decode #v[Opcode.keccak.busCode, addressOfIndex 6, addressOfIndex 7, addressOfIndex 6, addressOfIndex 7, addressOfIndex 8, addressOfIndex 12, addressOfIndex 13, addressOfIndex 17,
  0, g, 1, 0] = none

-- `KECCAK`'s output flags `(out_two, out_all)`: `one = (0, 0)`, `two = (1, 0)`, `all = (1, 1)`
-- (`OutCells::flags`, `isa.rs` at leanVM main `40f877dc`); `(0, 1)` and a non-bit
-- are none.
#guard keccakOutputFlags .one = (0, 0)
#guard keccakOutputFlags .two = (1, 0)
#guard keccakOutputFlags .all = (1, 1)
#guard outCells? 0 0 = some .one
#guard outCells? 1 0 = some .two
#guard outCells? 1 1 = some .all
#guard outCells? 0 1 = none
#guard outCells? g 0 = none
#guard outCells? 1 g = none
#guard decode (busEntry (.keccak ![1, g, addressOfIndex 2, addressOfIndex 3] (addressOfIndex 4) (addressOfIndex 8) (addressOfIndex 9) (addressOfIndex 13) true false .one)) =
  some (.keccak ![1, g, addressOfIndex 2, addressOfIndex 3] (addressOfIndex 4) (addressOfIndex 8)
      (addressOfIndex 9) (addressOfIndex 13) true false .one)
-- The output flag pair `(0, 1)` is no `OutCells`, nor is a non-bit output flag: no `KECCAK` entry
-- has them, so no `KECCAK` row reads them off the bytecode bus.
#guard decode #v[Opcode.keccak.busCode, addressOfIndex 6, addressOfIndex 7, addressOfIndex 6, addressOfIndex 7, addressOfIndex 8, addressOfIndex 12, addressOfIndex 13, addressOfIndex 17,
  0, 1, 0, 1] = none
#guard decode #v[Opcode.keccak.busCode, addressOfIndex 6, addressOfIndex 7, addressOfIndex 6, addressOfIndex 7, addressOfIndex 8, addressOfIndex 12, addressOfIndex 13, addressOfIndex 17,
  0, 1, g, 0] = none
#guard decode #v[Opcode.keccak.busCode, addressOfIndex 6, addressOfIndex 7, addressOfIndex 6, addressOfIndex 7, addressOfIndex 8, addressOfIndex 12, addressOfIndex 13, addressOfIndex 17,
  0, 1, 1, g] = none

/-- As a theorem: the flag pair `(1, 1)` is no mode's flags, so the vector is no instruction's
entry. -/
example : decode #v[Opcode.deref.busCode, addressOfIndex 4, 1, addressOfIndex 5, 1, 1, 0, 0, 0, 0,
    0, 0, 0] = none := by
  refine decode_eq_none_iff.mpr fun i h ↦ ?_
  have h0 := congrArg (fun v : Vector K 13 ↦ v[0]) h
  have h4 := congrArg (fun v : Vector K 13 ↦ v[4]) h
  have h5 := congrArg (fun v : Vector K 13 ↦ v[5]) h
  cases i <;> simp [busEntry, Opcode.code_injective.eq_iff] at h0 h4 h5
  rename_i mode
  cases mode <;> simp [derefFlags] at h4 h5

/-- The same, decided by the kernel. -/
example : decode #v[Opcode.deref.busCode, addressOfIndex 4, 1, addressOfIndex 5, 1, 1, 0, 0, 0, 0,
    0, 0, 0] = none := by
  decide +kernel

end
end LeanVMTests.Arithmetization
