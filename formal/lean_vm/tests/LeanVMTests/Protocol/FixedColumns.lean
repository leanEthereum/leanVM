/-
  LeanVMTests.Protocol.FixedColumns

  Regression controls for public-column evaluation and coordinate order.
-/

module

public import LeanVM.Protocol.FixedColumns
meta import LeanVM.Protocol.FixedColumns
meta import LeanVM.Protocol.Field
meta import LeanVM.Parameters.Field
meta import CompPoly.Multilinear.Basic

/-!
# Fixed-column controls

The index column is evaluated in the specification's form and against the form with the two
coordinates swapped. The bytecode column uses two distinct instructions, a spare zero slot, the
native evaluation at a point outside `K`, and the slot bits reversed as the mutation; a program
of sixteen instructions of the six kinds with distinct operands is laid out as the Rust encoder
lays it out, slot by slot, and not instruction by instruction. No private witness is needed to
construct any of these columns.
-/

namespace LeanVMTests.Protocol

open LeanVM.Protocol LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open CompPoly CMlPolynomialEval

@[expose] public section

private def fixedColumnAnswer {n : ℕ} (q : Column n) (z : Vector E n) : E :=
  eval₂Mle q.values (algebraMap K E) z

/-! ## The index column -/

-- Cell `i` holds `g ^ i`, and the point `(0, 1)` of the cube is index 2.
#guard (idxColumn 2).values = #v[1, g, g ^ 2, g ^ 3]
#guard fixedColumnAnswer (idxColumn 2) #v[0, 1] = ofK (g ^ 2)
#guard fixedColumnAnswer (idxColumn 2) #v[y, y ^ 2] = idxColumnEval #v[y, y ^ 2]

-- The specification's characteristic-two form (§6.5) at `κ = 2`, written out: coordinate `k`
-- carries `g ^ (2 ^ k)`.
#guard fixedColumnAnswer (idxColumn 2) #v[y, y ^ 2] =
  (1 + y * (1 + ofK g)) * (1 + y ^ 2 * (1 + ofK (g ^ 2)))
-- High bit first evaluates a different column.
#guard fixedColumnAnswer (idxColumn 2) #v[y, y ^ 2] ≠
  (1 + y * (1 + ofK (g ^ 2))) * (1 + y ^ 2 * (1 + ofK g))

example (z : Vector E 2) : eval₂Mle (idxColumn 2).values (algebraMap K E) z =
    ∏ k : Fin 2, (1 + z[k] * (1 + algebraMap K E (g ^ (2 ^ k.val)))) :=
  (idxColumn_eval z).trans (idxColumnEval_eq z)

/-! ## The bytecode column -/

/-- A public fixture with two different opcodes. -/
def fixedColumnProgram : Program where
  logSize := 1
  logSize_le := by decide
  code i := if i.val = 0 then .xor 1 1 1 else .mulNative 1 1 1

-- The cell of instruction `i` and slot 3 holds the opcode; slot 15 is spare.
#guard (bytecodeColumn fixedColumnProgram).values[
    cubeIndex (k := 1) (m := 4) (0 : Fin 2) (3 : Fin 16)] = Opcode.xor.code
#guard (bytecodeColumn fixedColumnProgram).values[
    cubeIndex (k := 1) (m := 4) (1 : Fin 2) (3 : Fin 16)] = Opcode.mulNative.code
#guard (List.finRange 2).all fun i ↦
  (bytecodeColumn fixedColumnProgram).values[cubeIndex (k := 1) (m := 4) i (15 : Fin 16)] = 0

example : eval₂Mle (bytecodeColumn fixedColumnProgram).values (algebraMap K E)
      (#v[y] ++ #v[0, 1, y, y ^ 2]) =
    bytecodeColumnEval fixedColumnProgram #v[y] #v[0, 1, y, y ^ 2] :=
  bytecodeColumn_eval fixedColumnProgram _ _

-- Instruction bit 1 selects the second instruction; slot 3 has bits (1,1,0,0).
#guard fixedColumnAnswer (bytecodeColumn fixedColumnProgram)
    ((#v[1] : Vector E 1) ++ (#v[1, 1, 0, 0] : Vector E 4)) = ofK Opcode.mulNative.code
-- Reversing the slot bits selects spare slot 12 and must not return the opcode.
#guard fixedColumnAnswer (bytecodeColumn fixedColumnProgram)
    ((#v[1] : Vector E 1) ++ (#v[0, 0, 1, 1] : Vector E 4)) = 0
#guard fixedColumnAnswer (bytecodeColumn fixedColumnProgram)
    ((#v[1] : Vector E 1) ++ (#v[0, 0, 1, 1] : Vector E 4)) ≠ ofK Opcode.mulNative.code

-- The same cube point written with the index and the slot: instruction 1, slot 3.
#guard fixedColumnAnswer (bytecodeColumn fixedColumnProgram)
    ((boolVec (1 : Fin (2 ^ 1)) : Vector E 1) ++ (boolVec (m := 4) (3 : Fin 16) : Vector E 4)) =
  ofK Opcode.mulNative.code

-- The native evaluator agrees with the oracle at a point outside `K` and off the cube.
#guard fixedColumnAnswer (bytecodeColumn fixedColumnProgram)
    ((#v[y] : Vector E 1) ++ (#v[y + 1, y ^ 2, y, 1] : Vector E 4)) =
  bytecodeColumnEval fixedColumnProgram #v[y] #v[y + 1, y ^ 2, y, 1]
-- Mutation: with the slot coordinates reversed it does not.
#guard fixedColumnAnswer (bytecodeColumn fixedColumnProgram)
    ((#v[y] : Vector E 1) ++ (#v[y + 1, y ^ 2, y, 1] : Vector E 4)) ≠
  bytecodeColumnEval fixedColumnProgram #v[y] #v[1, y, y ^ 2, y + 1]

/-- With no instruction bits, the public program contains exactly one instruction. -/
def singletonColumnProgram : Program where
  logSize := 0
  logSize_le := by decide
  code _ := .xor 1 1 1

#guard fixedColumnAnswer (bytecodeColumn singletonColumnProgram)
    ((#v[] : Vector E 0) ++ (#v[1, 1, 0, 0] : Vector E 4)) = ofK Opcode.xor.code
#guard fixedColumnAnswer (bytecodeColumn singletonColumnProgram)
    ((#v[] : Vector E 0) ++ (#v[1, 1, 1, 1] : Vector E 4)) = 0

example (w : Vector E 4) : eval₂Mle (bytecodeColumn singletonColumnProgram).values
    (algebraMap K E) ((#v[] : Vector E 0) ++ w) = bytecodeColumnEval singletonColumnProgram #v[] w :=
  bytecodeColumn_eval singletonColumnProgram _ _

/-! ## Sixteen instructions against the Rust encoder -/

/-- Sixteen instructions of the six kinds, with the distinct operands `K.ofBits 1` to
`K.ofBits 58` in order of appearance, and the three `DEREF` modes. -/
def sixteen : Program where
  logSize := 4
  logSize_le := by decide
  code := ![
    .xor (K.ofBits 1) (K.ofBits 2) (K.ofBits 3),
    .mulNative (K.ofBits 4) (K.ofBits 5) (K.ofBits 6),
    .setConstant (K.ofBits 7) (E.ofLimbs (K.ofBits 8) (K.ofBits 9) (K.ofBits 10)),
    .deref (K.ofBits 11) (K.ofBits 12) (K.ofBits 13) .cell,
    .jump (K.ofBits 14) (K.ofBits 15) (K.ofBits 16),
    .blake2s ![K.ofBits 17, K.ofBits 18, K.ofBits 19, K.ofBits 20] (K.ofBits 21) (K.ofBits 22)
      (K.ofBits 23),
    .deref (K.ofBits 24) (K.ofBits 25) (K.ofBits 26) .pc,
    .deref (K.ofBits 27) (K.ofBits 28) (K.ofBits 29) .fp,
    .xor (K.ofBits 30) (K.ofBits 31) (K.ofBits 32),
    .mulNative (K.ofBits 33) (K.ofBits 34) (K.ofBits 35),
    .setConstant (K.ofBits 36) (E.ofLimbs (K.ofBits 37) (K.ofBits 38) (K.ofBits 39)),
    .jump (K.ofBits 40) (K.ofBits 41) (K.ofBits 42),
    .blake2s ![K.ofBits 43, K.ofBits 44, K.ofBits 45, K.ofBits 46] (K.ofBits 47) (K.ofBits 48)
      (K.ofBits 49),
    .xor (K.ofBits 50) (K.ofBits 51) (K.ofBits 52),
    .mulNative (K.ofBits 53) (K.ofBits 54) (K.ofBits 55),
    .jump (K.ofBits 56) (K.ofBits 57) (K.ofBits 58)]

/-- Sixteen zero cells: a slot no public column fills. -/
def zeroSlot : List K := List.replicate 16 0

/-- Slot 3, the opcodes, one per instruction. -/
def opcodeSlot : List K :=
  [Opcode.xor.code, Opcode.mulNative.code, Opcode.setConstant.code, Opcode.deref.code,
    Opcode.jump.code, Opcode.blake2s.code, Opcode.deref.code, Opcode.deref.code, Opcode.xor.code,
    Opcode.mulNative.code, Opcode.setConstant.code, Opcode.jump.code, Opcode.blake2s.code,
    Opcode.xor.code, Opcode.mulNative.code, Opcode.jump.code]

/-- Slot 4, the first operand of every instruction. -/
def slot4 : List K :=
  [K.ofBits 1, K.ofBits 4, K.ofBits 7, K.ofBits 11, K.ofBits 14, K.ofBits 17, K.ofBits 24,
    K.ofBits 27, K.ofBits 30, K.ofBits 33, K.ofBits 36, K.ofBits 40, K.ofBits 43, K.ofBits 50,
    K.ofBits 53, K.ofBits 56]

/-- Slot 5, the second operand: `SET_CONSTANT`'s first limb, `BLAKE2S`'s second message
cell. -/
def slot5 : List K :=
  [K.ofBits 2, K.ofBits 5, K.ofBits 8, K.ofBits 12, K.ofBits 15, K.ofBits 18, K.ofBits 25,
    K.ofBits 28, K.ofBits 31, K.ofBits 34, K.ofBits 37, K.ofBits 41, K.ofBits 44, K.ofBits 51,
    K.ofBits 54, K.ofBits 57]

/-- Slot 6, the third operand. -/
def slot6 : List K :=
  [K.ofBits 3, K.ofBits 6, K.ofBits 9, K.ofBits 13, K.ofBits 16, K.ofBits 19, K.ofBits 26,
    K.ofBits 29, K.ofBits 32, K.ofBits 35, K.ofBits 38, K.ofBits 42, K.ofBits 45, K.ofBits 52,
    K.ofBits 55, K.ofBits 58]

/-- Slot 7: `SET_CONSTANT`'s top limb, `BLAKE2S`'s fourth message cell, the first `DEREF`
flag (`1` for the `pc` mode), zero for the rest. -/
def slot7 : List K :=
  [0, 0, K.ofBits 10, 0, 0, K.ofBits 20, 1, 0, 0, 0, K.ofBits 39, 0, K.ofBits 46, 0, 0, 0]

/-- Slot 8: `BLAKE2S`'s chaining-value operand and the second `DEREF` flag (`1` for the `fp`
mode). -/
def slot8 : List K := [0, 0, 0, 0, 0, K.ofBits 21, 0, 1, 0, 0, 0, 0, K.ofBits 47, 0, 0, 0]

/-- Slot 9: `BLAKE2S`'s output operand. -/
def slot9 : List K := [0, 0, 0, 0, 0, K.ofBits 22, 0, 0, 0, 0, 0, 0, K.ofBits 48, 0, 0, 0]

/-- Slot 10: `BLAKE2S`'s metadata operand. -/
def slot10 : List K := [0, 0, 0, 0, 0, K.ofBits 23, 0, 0, 0, 0, 0, 0, K.ofBits 49, 0, 0, 0]

/-- The table `stacked_bytecode_table` builds (`crates/leanvm_core/src/leaf.rs:558-577` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`): sixteen slots of `2 ^ κ_bc` cells, the cell
`(slot << κ_bc) + i` holding column `slot` at instruction `i`; the eight public columns at
slots 3 to 10 (`BYTECODE_PUBLIC_SLOT = 3`), and zero at the other slots. -/
def rustTable : List K :=
  zeroSlot ++ zeroSlot ++ zeroSlot ++ opcodeSlot ++ slot4 ++ slot5 ++ slot6 ++ slot7 ++ slot8 ++
    slot9 ++ slot10 ++ zeroSlot ++ zeroSlot ++ zeroSlot ++ zeroSlot ++ zeroSlot

-- The column is the Rust's table, cell for cell.
#guard (bytecodeColumn sixteen).values.toList = rustTable
-- Mutation: the instruction-major layout, the sixteen slots of each instruction in turn, is
-- another table.
#guard (bytecodeColumn sixteen).values.toList ≠
  (List.finRange 16).flatMap fun i ↦ (encodeSlots (sixteen.code i)).toList

end
end LeanVMTests.Protocol
