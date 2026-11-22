/-
  LeanVM.Guest.B1.Digest.ClaimListCBig5

  `claim_list_digest`'s big frame loop `claim_list_chain_loop0`, evaluated: part 5 of `grpcOk`
  (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCBigDefs
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«claim_list_chain_loop0»

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 100000 in
theorem big_c5 : (stLoadsOk bigF (.n (val% «claim_list_chain_loop0» "st")) (grpSt 565) 0 &&
    monoIs ((loopAtoms bigFn).filter pureB) (.n (val% «claim_list_chain_loop0» "st")) (.n (val% «claim_list_chain_loop0» "chain")) (.n (val% «claim_list_chain_loop0» "xq")) 13 &&
    monoIs ((loopAtoms bigFn).filter pureB) (.n (val% «claim_list_chain_loop0» "blk")) (.n (val% «claim_list_chain_loop0» "entries_ptr")) (.n (val% «claim_list_chain_loop0» "xq")) (4 * 136)) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
