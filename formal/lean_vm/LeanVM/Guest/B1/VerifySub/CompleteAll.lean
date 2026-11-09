/-
  LeanVM.Guest.B1.VerifySub.CompleteAll

  `verify_sub` is complete with no hypothesis left: `verify_keccak`'s completeness discharged.
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteB
public import LeanVM.Guest.B1.KeccakGkr.VkCV
public import LeanVM.Guest.B1.KeccakGkr.VkCW

/-!
# `verify_sub`, complete

* `verify_sub_complete_all`: `verify_sub_complete_Spec` for the guest's `2^23` bytecode words,
  `verify_keccak`'s placed completeness (`verify_keccak_completeAt`) discharging the last callee.
* `verify_sub_completeB_fs`: the bounded form at the deployed frame sizes `B2C.fs`, within
  `vsBound W vkBound` words for the callees' words facts `W : VsWords B2C.fs`
  (`verify_keccak_completeAtB_fs`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main

@[expose] public section

end
end LeanVM.Guest.B1.VerifySub
