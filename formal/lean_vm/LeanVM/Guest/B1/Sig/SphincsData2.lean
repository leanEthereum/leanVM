/-
  LeanVM.Guest.B1.Sig.SphincsData2

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sAfterDigest` after
  the digest block, on the statements from `at@462~0`'s to the end.
-/

module

public import LeanVM.Guest.Pack.verify_sig_lean_sphincs.Core
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Common.Basic
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sig_lean_sphincs»

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem sAfterDigest_slice_3000 :
    (((Fn.«verify_sig_lean_sphincs».core).body.drop (pos% «verify_sig_lean_sphincs» "s40#0")).drop (span% «verify_sig_lean_sphincs» "a0_b~0" "at@462~0")).take (span% «verify_sig_lean_sphincs» "at@462~0" "check[0]@221") = (sAfterDigest.drop
        3000).take 500 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sAfterDigest_slice_3500 :
    (((Fn.«verify_sig_lean_sphincs».core).body.drop (pos% «verify_sig_lean_sphincs» "s40#0")).drop (span% «verify_sig_lean_sphincs» "a0_b~0" "check[0]@221")).take (span% «verify_sig_lean_sphincs» "check[0]@221" "s53.i0:sp_layer.s2.i0:sp_from_bytes.s0.u2.s1#0") = (sAfterDigest.drop
        3500).take 500 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sAfterDigest_drop_4000 :
    ((Fn.«verify_sig_lean_sphincs».core).body.drop (pos% «verify_sig_lean_sphincs» "s40#0")).drop (span% «verify_sig_lean_sphincs» "a0_b~0" "s53.i0:sp_layer.s2.i0:sp_from_bytes.s0.u2.s1#0") = sAfterDigest.drop 4000 :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Sig
