/-
  LeanVM.Guest.B1.Digest.ClaimListCBig1

  `claim_list_digest`'s big frame loop `claim_list_digest_loop0`, evaluated: part 1 of `grpcOk`
  (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCBigDefs
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 100000 in
theorem big_c1 : (loopShapeF bigFn name% «claim_list_digest_loop0» && (chk 4 bigFn.body).isSome &&
    (loopPre bigFn).all isAtomS && atomsEqbL (atomsIn (loopPre bigFn)) (loopAtoms bigFn)) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
