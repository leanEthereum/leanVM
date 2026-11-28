/-
  LeanVM.Facts.BytecodeShape

  A deferred claim of the bytecode's shape.
-/

module

public import Statement.LeanVmGuest
public import LeanVM.Protocol.Verifier.ClaimHolds

@[expose] public section

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- The deferred claim has the shape of the bytecode `bytecode`: a point of `log₂` of its length
(`bytecode_vars`, `crates/aggregation/src/deferred.rs`; `BYTECODE_VARS`, `lean_ethereum.py`). -/
def _root_.LeanVM.Protocol.Verifier.BytecodeClaim.HasBytecodeShape (bytecode : List K) (claim : BytecodeClaim) :
    Prop :=
  claim.bytecodePoint.length = Nat.log2 bytecode.length

end LeanVM.Node

end
