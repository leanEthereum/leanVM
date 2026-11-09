/-
  LeanVM.Guest.B1.Digest.ClaimListCBig3

  `claim_list_digest`'s big frame loop `__loop15`, evaluated: part 3 of `grpcOk` (kernel evaluation, the known values a bit mask).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCBigDefs
public import LeanVM.Guest.B1.Fwd.CanonB

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 100000 in
theorem big_c3 : canonChk ((grpSt 565).map V.idx ++ (List.range (4 * 136)).map (· + 21)) bigF = true :=
  canonChk_of_canonGoB (by decide +kernel)

end
end LeanVM.Guest.B1.Digest
