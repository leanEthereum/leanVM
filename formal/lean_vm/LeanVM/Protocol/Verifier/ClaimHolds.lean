/-
  LeanVM.Protocol.Verifier.ClaimHolds

  A bytecode claim true of the bytecode, its value only.
-/

module

public import Statement.Verifier.Lib

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics

/-- The claim's value is the bytecode's multilinear extension at its point (the value only;
`BytecodeClaim.HoldsWithShape` adds the power-of-two length). -/
def BytecodeClaim.Holds (bytecode : List K) (claim : BytecodeClaim) : Prop :=
  multilinearEval (bytecode.map ofK) claim.bytecodePoint = claim.bytecodeValue

end LeanVM.Protocol.Verifier

end
