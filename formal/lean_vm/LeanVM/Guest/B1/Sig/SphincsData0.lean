/-
  LeanVM.Guest.B1.Sig.SphincsData0

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sAfterDigest` after
  the digest block, on statements `a0_b~0 ..< parent[0]@86`.
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
theorem sAfterDigest_slice_0 :
    (((Fn.«verify_sig_lean_sphincs».core).body.drop (pos% «verify_sig_lean_sphincs» "s40#0")).drop 0).take (span% «verify_sig_lean_sphincs» "a0_b~0" "at@69") = (sAfterDigest.drop
        0).take
        500 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sAfterDigest_slice_500 :
    (((Fn.«verify_sig_lean_sphincs».core).body.drop (pos% «verify_sig_lean_sphincs» "s40#0")).drop (span% «verify_sig_lean_sphincs» "a0_b~0" "at@69")).take (span% «verify_sig_lean_sphincs» "at@69" "at@146~0") = (sAfterDigest.drop
        500).take 500 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sAfterDigest_slice_1000 :
    (((Fn.«verify_sig_lean_sphincs».core).body.drop (pos% «verify_sig_lean_sphincs» "s40#0")).drop (span% «verify_sig_lean_sphincs» "a0_b~0" "at@146~0")).take (span% «verify_sig_lean_sphincs» "at@146~0" "parent[0]@86") = (sAfterDigest.drop
        1000).take 500 :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Sig
