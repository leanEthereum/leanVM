/-
  LeanVM.Guest.B1.Digest.ClaimListCBig4

  `claim_list_digest`'s big frame loop `__loop15`, evaluated: part 4 of `grpcOk` (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCBigDefs

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 100000 in
theorem big_c4 : (loopAtoms bigFn).all (fun a => !needsSide a || decide (a ∈ bigS) ||
    isLoadBelow 9 13 a || isLoadBelow 20 (4 * 136) a) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
