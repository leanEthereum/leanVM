/-
  LeanVM.Guest.B1.Sig.SphincsData2

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sAfterDigest` after
  the digest block, on statements 4358 to 5662.
-/

module

public import LeanVM.Guest.Pack.verify_sig_lean_sphincs.Core
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Common.Basic

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem sAfterDigest_slice_3000 :
    (((Fn.«verify_sig_lean_sphincs».core).body.drop 1358).drop 3000).take 500 = (sAfterDigest.drop
        3000).take 500 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sAfterDigest_slice_3500 :
    (((Fn.«verify_sig_lean_sphincs».core).body.drop 1358).drop 3500).take 500 = (sAfterDigest.drop
        3500).take 500 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sAfterDigest_drop_4000 :
    ((Fn.«verify_sig_lean_sphincs».core).body.drop 1358).drop 4000 = sAfterDigest.drop 4000 :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Sig
