module

public import LeanVM.Semantics.Lemmas
meta import Statement.LeanIsa
meta import Statement.Fast.QuadExt
meta import Statement.Fast.FieldWords

/-!
# Tests: instructions, programs, and fetch

A four-instruction program, one per address `g ^ 0, …, g ^ 3`, fetched by address through the
fetch lemmas, since `LeanIsaProgram.fetch` is noncomputable. The last slot `g ^ 3` fetches its typed
instruction; the one-past-end address `g ^ 4` and counter `0` fetch nothing. The bytecode cap
is inhabited at its maximum (`2 ^ 32` instructions), and
`fetch_gpow` applies there. Instruction equality is decidable and compiled, which the bytecode
decoder tests need.
-/

namespace LeanVMTests.Semantics

open LeanVM.Parameters LeanVM.Semantics

public section

/-! ## A program -/

def i0 : LeanIsaInstruction := .setConstant (addressOfIndex 2) (E.ofLimbs (K.ofBits 7) 0)
def i1 : LeanIsaInstruction := .xor (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4)
def i2 : LeanIsaInstruction := .deref (addressOfIndex 4) 1 (addressOfIndex 5) .pc
def i3 : LeanIsaInstruction := .jump (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4)

/-- Four instructions: `logSize = 2`. -/
def prog : LeanIsaProgram := ⟨2, by decide, ![i0, i1, i2, i3]⟩

example : prog.fetch 1 = some i0 := by simpa [prog] using prog.fetch_gpow 0
example : prog.fetch g = some i1 := by simpa [prog] using prog.fetch_gpow 1
example : prog.fetch (addressOfIndex 2) = some i2 := prog.fetch_gpow 2
example : prog.fetch (addressOfIndex 3) = some i3 := prog.fetch_gpow 3
-- The sentinel slot is the last instruction; one past it, and `0`, fetch nothing.
example : prog.fetch (addressOfIndex 4) = none := by
  rw [LeanIsaProgram.fetch, gLog?_gpow_eq_none (by decide) (by decide), Option.map_none]
example : prog.fetch 0 = none := prog.fetch_zero

/-! ## Opcodes -/

#guard i0.opcode = .setConstant
#guard i1.opcode = .xor
#guard i2.opcode = .deref
#guard i3.opcode = .jump
#guard (LeanIsaInstruction.mulNative 1 g (addressOfIndex 2)).opcode = .mulNative
#guard (LeanIsaInstruction.keccak ![1, g, addressOfIndex 2, addressOfIndex 3] (addressOfIndex 4) (addressOfIndex 8) (addressOfIndex 9) (addressOfIndex 13) false true .all).opcode = .keccak

/-! ## Equality -/

#guard LeanIsaInstruction.keccak ![1, g, addressOfIndex 2, addressOfIndex 3] (addressOfIndex 4)
    (addressOfIndex 8) (addressOfIndex 9) (addressOfIndex 13) false true .all =
  LeanIsaInstruction.keccak ![1, g, addressOfIndex 2, addressOfIndex 3] (addressOfIndex 4)
      (addressOfIndex 8) (addressOfIndex 9) (addressOfIndex 13) false true .all
#guard LeanIsaInstruction.keccak ![1, g, addressOfIndex 2, addressOfIndex 3] (addressOfIndex 4)
    (addressOfIndex 8) (addressOfIndex 9) (addressOfIndex 13) false true .all ≠
  LeanIsaInstruction.keccak ![1, g, addressOfIndex 2, addressOfIndex 5] (addressOfIndex 4)
      (addressOfIndex 8) (addressOfIndex 9) (addressOfIndex 13) false true .all
#guard LeanIsaInstruction.keccak ![1, g, addressOfIndex 2, addressOfIndex 3] (addressOfIndex 4)
    (addressOfIndex 8) (addressOfIndex 9) (addressOfIndex 13) false true .all ≠
  LeanIsaInstruction.keccak ![1, g, addressOfIndex 2, addressOfIndex 3] (addressOfIndex 4)
      (addressOfIndex 8) (addressOfIndex 9) (addressOfIndex 13) true true .all
#guard LeanIsaInstruction.keccak ![1, g, addressOfIndex 2, addressOfIndex 3] (addressOfIndex 4)
    (addressOfIndex 8) (addressOfIndex 9) (addressOfIndex 13) false false .one ≠
  LeanIsaInstruction.keccak ![1, g, addressOfIndex 2, addressOfIndex 3] (addressOfIndex 4)
      (addressOfIndex 8) (addressOfIndex 9) (addressOfIndex 13) false false .two
#guard LeanIsaInstruction.deref 1 g (addressOfIndex 2) .pc ≠ LeanIsaInstruction.deref 1 g
    (addressOfIndex 2) .fp
#guard LeanIsaInstruction.setConstant 1 (E.ofLimbs 1 (K.ofBits 3)) ≠ LeanIsaInstruction.setConstant 1 (E.ofLimbs 1 (K.ofBits 4))

/-! ## The bytecode cap -/

/-- The largest program the cap admits, `2 ^ 32` copies of `i0`. -/
def largest : LeanIsaProgram := ⟨maxLogBytecode, le_rfl, fun _ ↦ i0⟩

/-- Fetching the last slot of the largest program. -/
example : largest.fetch (addressOfIndex (2 ^ 32 - 1)) = some i0 :=
  largest.fetch_gpow ⟨2 ^ 32 - 1, by decide⟩

/-- `2 ^ 33` instructions is not a program. -/
example : ¬ 33 ≤ maxLogBytecode := by decide

end
end LeanVMTests.Semantics
