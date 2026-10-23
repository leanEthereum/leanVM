module

public import LeanVM.Semantics.Lemmas
meta import LeanVM.Spec.Isa

/-!
# Tests: instructions, programs, and fetch

A four-instruction program, one per address `g ^ 0, …, g ^ 3`, fetched by address through the
fetch lemmas, since `Program.fetch` is noncomputable. The last slot `g ^ 3` fetches its typed
instruction; the one-past-end address `g ^ 4` and counter `0` fetch nothing. The bytecode cap
is inhabited at its maximum (`2 ^ 32` instructions), and
`fetch_gpow` applies there. Instruction equality is decidable and compiled, which the bytecode
decoder tests need.
-/

namespace LeanVMTests.Semantics

open LeanVM.Parameters LeanVM.Semantics

public section

/-! ## A program -/

def i0 : Instr := .setConstant (gpow 2) (E.ofLimbs (K.ofBits 7) 0 0)
def i1 : Instr := .xor (gpow 2) (gpow 3) (gpow 4)
def i2 : Instr := .deref (gpow 4) 1 (gpow 5) .pc
def i3 : Instr := .jump (gpow 2) (gpow 3) (gpow 4)

/-- Four instructions: `logSize = 2`. -/
def prog : Program := ⟨2, by decide, ![i0, i1, i2, i3]⟩

example : prog.fetch 1 = some i0 := by simpa [prog] using prog.fetch_gpow 0
example : prog.fetch g = some i1 := by simpa [prog] using prog.fetch_gpow 1
example : prog.fetch (gpow 2) = some i2 := prog.fetch_gpow 2
example : prog.fetch (gpow 3) = some i3 := prog.fetch_gpow 3
-- The sentinel slot is the last instruction; one past it, and `0`, fetch nothing.
example : prog.fetch (gpow 4) = none := by
  rw [Program.fetch, gLog?_gpow_eq_none (by decide) (by decide), Option.map_none]
example : prog.fetch 0 = none := prog.fetch_zero

/-! ## Opcodes -/

#guard i0.opcode = .setConstant
#guard i1.opcode = .xor
#guard i2.opcode = .deref
#guard i3.opcode = .jump
#guard (Instr.mulNative 1 g (gpow 2)).opcode = .mulNative
#guard (Instr.blake2s ![1, g, gpow 2, gpow 3] (gpow 4) (gpow 6) (gpow 8)).opcode = .blake2s

/-! ## Equality -/

#guard Instr.blake2s ![1, g, gpow 2, gpow 3] (gpow 4) (gpow 6) (gpow 8) =
  Instr.blake2s ![1, g, gpow 2, gpow 3] (gpow 4) (gpow 6) (gpow 8)
#guard Instr.blake2s ![1, g, gpow 2, gpow 3] (gpow 4) (gpow 6) (gpow 8) ≠
  Instr.blake2s ![1, g, gpow 2, gpow 5] (gpow 4) (gpow 6) (gpow 8)
#guard Instr.deref 1 g (gpow 2) .pc ≠ Instr.deref 1 g (gpow 2) .fp
#guard Instr.setConstant 1 (E.ofLimbs 1 (K.ofBits 2) (K.ofBits 3)) ≠ Instr.setConstant 1 (E.ofLimbs 1 (K.ofBits 2) (K.ofBits 4))

/-! ## The bytecode cap -/

/-- The largest program the cap admits, `2 ^ 32` copies of `i0`. -/
def largest : Program := ⟨maxLogBytecode, le_rfl, fun _ ↦ i0⟩

/-- Fetching the last slot of the largest program. -/
example : largest.fetch (gpow (2 ^ 32 - 1)) = some i0 :=
  largest.fetch_gpow ⟨2 ^ 32 - 1, by decide⟩

/-- `2 ^ 33` instructions is not a program. -/
example : ¬ 33 ≤ maxLogBytecode := by decide

end
end LeanVMTests.Semantics
