/-
  LeanVM.Guest.Compiled

  The guest's code as the compiler lays it out: compiled functions, in chunks, assembled into a
  program. A notion of the proofs, not of the statement, which reads the guest's code as one list
  (`Statement/LeanVmGuest.lean`, `guestProgram`).
-/

module

public import Statement.LeanIsa

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- The instructions per chunk of a compiled function's code. -/
def chunkSize : ℕ := 2048

/-- Element `n` of a list, `fallback` past its end; structural, for the kernel. -/
def listElementOrDefault {α : Type} : List α → ℕ → α → α
  | [], _, fallback => fallback
  | a :: _, 0, _ => a
  | _ :: as, n + 1, fallback => listElementOrDefault as n fallback

/-- A compiled function: its name (`f__L…` for a specialization), entry pc, number of
instructions, and code in chunks of `chunkSize` instructions (the last shorter). -/
structure CompiledFunction where
  /-- Its name, for a reader of the generated data. -/
  name : String
  /-- The pc of its first instruction. -/
  entryPc : ℕ
  /-- Its number of instructions. -/
  instructionCount : ℕ
  /-- Its code, in chunks of `chunkSize` instructions. -/
  chunks : List (List OffsetInstruction)

/-- The instruction at offset `i`, the padding past the end. -/
def CompiledFunction.instructionAt (f : CompiledFunction) (i : ℕ) : OffsetInstruction :=
  listElementOrDefault (listElementOrDefault f.chunks (i / chunkSize) []) (i % chunkSize) .padding

/-- The instruction at pc `pc` of the functions `functions`, the padding outside them: the first
function whose end exceeds `pc` holds it. It reads the functions as laid out one after another
(`Code.lean`'s `consecutive`, decided for the guest in `Bytecode.lean`). -/
def instructionAtPc : List CompiledFunction → ℕ → OffsetInstruction
  | [], _ => .padding
  | f :: fs, pc => if pc < f.entryPc + f.instructionCount then f.instructionAt (pc - f.entryPc) else
      instructionAtPc fs pc

/-- The program of `2^logSize` slots holding the functions `functions`, padded. -/
def assemble (functions : List CompiledFunction) (logSize : ℕ)
    (logSize_le : logSize ≤ maxLogBytecode) : LeanIsaProgram :=
  ⟨logSize, logSize_le, fun i ↦ (instructionAtPc functions i).toLeanIsaInstruction⟩

end

end LeanVM.Guest
