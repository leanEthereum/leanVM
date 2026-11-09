/-
  LeanVM.Guest.B1.Digest.ClaimListCBig2

  `claim_list_digest`'s big frame loop `__loop15`, evaluated: part 2 of `grpcOk` (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCBigDefs

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 100000 in
theorem big_c2 : bigS.all (fun a => (List.range 13).any fun c =>
    atomEqb a (.load (bigCSpec.outV (bigCSpec.nb - 1) c) (.n 9) (13 + c))) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
