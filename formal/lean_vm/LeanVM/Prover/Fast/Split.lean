import LeanVM.Prover.Fast.Arith
import Statement.Verifier.Lib

/-!
# The program's split, compiled with the program in an array

`splitAt` (`Bytecode::split`, `Statement/Verifier/Layout.lean`) reads slot `s` of instruction `k`
with `List.getD`, a walk of the program per read, so its compiled form is quadratic in the program's
length: the guest's `2^23` words are out of reach. `splitAt.fast` reads them from the program as an
array, with `E`'s product on machine words (`mulE`), and is `@[csimp]`, as is `computedSplit.fast`,
`computedSplit` compiled where that lemma acts; `Fast/Prover.lean` imports them before it copies the
verifier, so the copies of `computedSplit`'s callers call them.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Prover.Fast

/-- `splitAt`, its slots read from an array. -/
def splitAt.fast (bytecode : List K) (point : List E) (pc : List (ℕ × ℕ)) : Split :=
  let words := bytecode.toArray
  let n := bytecode.length >>> bytecodeSlotBits
  let slot := fun (s k : ℕ) ↦ words.getD (s * n + k) 0
  let rows := ((eqKernel point).zip (powers gen (2 ^ point.length))).zipIdx
  let ops := List.range (opKeccak + 1)
  let sumOp := fun (F : ℕ) (term : E → E → ℕ → E) ↦
    sumE (rows.map fun ((e, gk), k) ↦ if opcodeOf (slot 3 k) = F then term e gk k else 0)
  { count := ops.map fun F ↦ sumOp F fun e _ _ ↦ e
    slots := ops.map fun F ↦ (List.range (2 ^ bytecodeSlotBits)).map fun s ↦
      if 4 ≤ s then sumOp F fun e _ k ↦ mulE e (ofK (slot s k)) else 0
    pc := ops.map fun F ↦ (List.range (2 ^ bytecodeSlotBits)).map fun s ↦
      if 4 ≤ s ∧ pc.contains (F, s) then sumOp F fun e gk k ↦ mulE e (mulE gk (ofK (slot s k)))
      else 0 }

/-- An array's entry is its list's. -/
theorem toArray_getD (l : List K) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp only [Array.getD, List.getD_eq_getElem?_getD, List.size_toArray]
  by_cases h : i < l.length <;> simp [h]

@[csimp] theorem splitAt.fast_eq : @splitAt = @splitAt.fast := by
  funext bytecode point pc
  simp only [splitAt, splitAt.fast, toArray_getD, mulE]

/-- `computedSplit`, compiled here, so that it calls `splitAt.fast`: the statement's own compiled
`computedSplit` calls the statement's `splitAt`. -/
def computedSplit.fast (bytecode : List K) (point : List E) (pc : List (ℕ × ℕ)) :
    Compile.VerifierProgram Split := do
  Compile.VerifierProgram.require
    (point.length < 64 ∧ bytecode.length >>> bytecodeSlotBits = 2 ^ point.length)
  return splitAt bytecode point pc

@[csimp] theorem computedSplit.fast_eq : @computedSplit = @computedSplit.fast := rfl

end LeanVM.Protocol.Verifier
