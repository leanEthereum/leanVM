/-
  LeanVM.Facts.BytecodeShape

  A deferred claim of the bytecode's shape.
-/

module

public import Statement.LeanVmGuest

@[expose] public section

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- The deferred claim has the shape of the bytecode `bytecode`: a point of `log₂` of its length
(`bytecode_vars`, `crates/aggregation/src/deferred.rs`; `BYTECODE_VARS`, `lean_ethereum.py`). -/
def DeferredBytecodeClaim.HasBytecodeShape (bytecode : List K) (claim : DeferredBytecodeClaim) : Prop :=
  claim.bytecodePoint.length = Nat.log2 bytecode.length

end LeanVM.Node

end
