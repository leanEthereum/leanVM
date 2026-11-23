module

public import NativeRustcVmArm.Spec.Top
public import NativeVm.Equiv.Execution
public import NativeVm.Wire.ModelSpec
public import NativeRustcVm.Wire.ModelFacts

/-!
# `leanvm_verify`'s verdict in the model's terms

`verdictWord` is `0` when the decoder refuses the bytes (`verdict_none`), else `Model.verify`'s
verdict on the decoded stream and openings (`verdict_some`): `decodeM_spec` (the decoder is
`Proof.fromBytes`), `decodeM_toProof` (its proof is the decoded arrays') and `verify_eq`
(`Model.verify` is `verifyWith`).
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeVm NativeVm.Wire NativeRustcVm.Wire
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

theorem verdict_none {bytes : List UInt8} (h : decodeM bytes = none) (bytecode : List UInt64)
    (pub : Vector UInt64 4) : verdictWord bytes bytecode pub = 0 := by
  unfold verdictWord
  rw [decodeM_spec, h]
  rfl

theorem verdict_some {bytes : List UInt8} {r : List E × List PhaseOut} (h : decodeM bytes = some r)
    (bytecode : List UInt64) (pub : Vector UInt64 4) :
    verdictWord bytes bytecode pub =
      if Model.verify bytecode.toArray pub (streamW r.1) (openingsW r.2) then 1 else 0 := by
  unfold verdictWord
  rw [decodeM_spec, h, NativeVm.Equiv.verify_eq]
  simp only [Option.map_some, Option.elim_some, decodeM_toProof h]

end

end NativeRustcVmArm.Top.Leanvm
