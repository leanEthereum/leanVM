import Rv64Verifier.Proofs.Layout.Repr

/-!
# `grow_one` with a fresh buffer

`Runtime.GrowOneSpec` says the grown buffer is allocated and starts with the old bytes, not that it
is new; a caller that writes into it needs that it misses everything allocated before. It is new:
`finish_grow` takes it from `alloc` (the bump allocator's `realloc` allocates and copies). Until the
runtime's contract says so, the layout proofs take this stronger one.
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 Rv64Verifier.Runtime

/-- `grow_one`, its new buffer fresh. -/
def GrowOneFreshSpec (entry : Word) (size align : Nat) : Prop :=
  FunSpec Image.code entry (GrowOnePre size align) fun s t ↦
    GrowOnePost size align s t ∧ heapNext s ≤ (vecPtr t (s.getReg .x10)).toNat

end Rv64Verifier.Layout
