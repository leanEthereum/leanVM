/-
  LeanVM.Guest.B1.Sig.SphincsData0

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sAfterDigest` after
  the digest block, on statements 1358 to 2857.
-/

module

public import LeanVM.Guest.Data.Names
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Common.Basic

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem sAfterDigest_slice_0 :
    (((fn% «verify_sig_lean_sphincs»).body.drop 1358).drop 0).take 500 = (sAfterDigest.drop 0).take
        500 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sAfterDigest_slice_500 :
    (((fn% «verify_sig_lean_sphincs»).body.drop 1358).drop 500).take 500 = (sAfterDigest.drop
        500).take 500 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sAfterDigest_slice_1000 :
    (((fn% «verify_sig_lean_sphincs»).body.drop 1358).drop 1000).take 500 = (sAfterDigest.drop
        1000).take 500 :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Sig
