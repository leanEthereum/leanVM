/-
  LeanVM.Guest.B1.Digest.ClaimListCBigDefs

  `claim_list_digest`'s big frame loop `__loop15` (136 claims, 64 blocks): the parts of `grpcOk`
  that `ClaimListCBig1`-`5` evaluate, each a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCChk

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `__loop15`. -/
noncomputable def bigFn : Fn := coreProgram.getD 330 default

/-- `__loop15`'s stores. -/
noncomputable def bigS : List Atom := storesOf 4 bigFn.body

/-- `__loop15`'s atoms but its stores. -/
noncomputable def bigF : List Atom := (loopAtoms bigFn).filter fun a => decide (a ∉ bigS)

/-- `__loop15`'s chain. -/
noncomputable def bigCSpec : ChainSpec := grpSpec 136 21 565 (loopAtoms bigFn)

end
end LeanVM.Guest.B1.Digest
