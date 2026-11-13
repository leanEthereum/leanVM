/-
  LeanVM.Guest.B1.Digest.ClaimListCBig5

  `claim_list_digest`'s big frame loop `claim_list_digest_loop0`, evaluated: part 5 of `grpcOk` (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCBigDefs

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 100000 in
theorem big_c5 : (stLoadsOk bigF (.n 9) (grpSt 565) 0 &&
    monoIs ((loopAtoms bigFn).filter pureB) (.n 9) (.n 2) (.n 0) 13 &&
    monoIs ((loopAtoms bigFn).filter pureB) (.n 20) (.n 3) (.n 0) (4 * 136)) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
