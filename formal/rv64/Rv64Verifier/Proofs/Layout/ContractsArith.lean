import Rv64Verifier.Proofs.Layout.ContractsBuild

/-!
# The contract of `flushes_arith`

As `ContractsBuild.lean`, but the `Flushes` is new: the function returns it through `a0`, so the
caller's slot holds nothing sound on entry, and every buffer the result reaches is allocated by
the call (`NewFlushes`, as `NewFormVec` for a `Vec<Form>`).
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Model.LayoutMirror

/-- What a constructor of a `Flushes` at `out` ensures: a sound value, every buffer it reaches
allocated by the call, and memory changed only at `out`, the `n` bytes below `sp`, `NEXT` and what
it allocates. -/
structure NewFlushes (s t : MachineState) (out : Word) (n : Nat) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  ok : FlushesOk t out
  fresh : ∀ x, flushesDeep t out x → Fresh s t x
  frame : DFrame s t fun a ↦ Within a out 48 ∨ Within a (stackLo s n) n ∨ Within a nextAddr 8 ∨
    Fresh s t a

/-! ## `flushes_arith`, at `0x8000547c` -/

/-- Its 480-byte frame, and `memory_cols`'s stack below it (the deepest of its callees'). -/
@[rv_addr] def flushesArithStack : Nat := 480 + memoryColsStack

/-- `a0` = where the `Flushes` goes; `a1` = `opcode`; `a2` = `multiply`, a `bool`. -/
structure FlushesArithPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s flushesArithStack
  out : ValidMemRange (s.getReg .x10) 6
  outFree : Outside s (s.getReg .x10) 48
  outStack : Apart (s.getReg .x10) 48 (stackLo s flushesArithStack) flushesArithStack
  rodata : RodataOk s

/-- `flushes_arith(opcode, multiply)`, `multiply` taken as `a2 != 0` (the code's test). -/
def FlushesArithSpec : Prop := FunSpec Image.code 0x8000547c FlushesArithPre fun s t ↦
  NewFlushes s t (s.getReg .x10) flushesArithStack ∧
    flushesOf t (s.getReg .x10) = flushesArithRust (s.getReg .x11).toNat (s.getReg .x12 != 0)

end Rv64Verifier.Layout
