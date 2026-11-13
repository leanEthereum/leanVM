/-
  LeanVM.Guest.B1.Sig.SphincsData1

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sAfterDigest` after
  the digest block, on statements 2858 to 4357.
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
theorem sAfterDigest_slice_1500 :
    (((Fn.«verify_sig_lean_sphincs».core).body.drop 1358).drop 1500).take 500 = (sAfterDigest.drop
        1500).take 500 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sAfterDigest_slice_2000 :
    (((Fn.«verify_sig_lean_sphincs».core).body.drop 1358).drop 2000).take 500 = (sAfterDigest.drop
        2000).take 500 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sAfterDigest_slice_2500 :
    (((Fn.«verify_sig_lean_sphincs».core).body.drop 1358).drop 2500).take 500 = (sAfterDigest.drop
        2500).take 500 :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Sig
