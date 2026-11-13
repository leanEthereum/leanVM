/-
  LeanVM.Guest.B1.Digest.ClaimListCBigDefs

  `claim_list_digest`'s big frame loop `claim_list_digest_loop0` (136 claims, 64 blocks): the parts of `grpcOk`
  that `ClaimListCBig1`-`5` evaluate, each a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCChk

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `claim_list_digest_loop0`. -/
noncomputable def bigFn : Fn := coreProgram.getD idx% «claim_list_digest_loop0» default

/-- `claim_list_digest_loop0`'s stores. -/
noncomputable def bigS : List Atom := storesOf 4 bigFn.body

/-- `claim_list_digest_loop0`'s atoms but its stores. -/
noncomputable def bigF : List Atom := (loopAtoms bigFn).filter fun a => decide (a ∉ bigS)

/-- `claim_list_digest_loop0`'s chain. -/
noncomputable def bigCSpec : ChainSpec := grpSpec 136 21 565 (loopAtoms bigFn)

end
end LeanVM.Guest.B1.Digest
