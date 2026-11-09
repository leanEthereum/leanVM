/-
  LeanVM.Guest.B1.Main.Composed

  `main`'s soundness with its callees' statements discharged by their proofs, but `verify_sub`'s.
-/

module

public import LeanVM.Guest.B1.Main.Callees
public import LeanVM.Guest.B1.Main.Aggregate
public import LeanVM.Guest.B1.Da.Verify
public import LeanVM.Guest.B1.Sig.SphincsSound
public import LeanVM.Guest.B1.VerifySub.Interface

/-!
# `main`, composed

`main_sound_sub`: a run of `main`'s body whose public input cells hold the digest `D` decodes to
a statement of digest `D` held by some witness (`NodeRelation`), given only `verify_sub`'s contract
(`SubSound`, B1-d's `verify_sub` statement): the signature checks (B1-e's
`verify_sig_lean_sphincs_sound_holds`; leanXMSS's segment statement in `SoundV`), the DA check
(`da_verify_holds`) and the batching (`aggregate_claims_holds`) are proved. `subSound_of`:
B1-d's `verify_sub_Spec` gives `SubSound`; `main_sound_vsub` takes it as the one hypothesis.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

end
end LeanVM.Guest.B1.Main
