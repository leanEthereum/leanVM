/-
  LeanVM.Guest.Exact.SphincsPinned

  `verify_sig_lean_sphincs`'s computed hints are its three bit hints of `H_msg`'s cells (`Sig.sBitsAtoms`), by the
  kernel.
-/

module

public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.Pack.verify_sig_lean_sphincs.Core
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sig_lean_sphincs»

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **The bit hints of `H_msg`'s cells** (`sBitsHint`'s atoms): `n17`'s and `n18`'s 128 bits, `n27`'s low 16. -/
def sBitsAtoms : List Atom :=
  [.hint (.bits (.n (val% «verify_sig_lean_sphincs» "d0[0]")) 0 128 (.stack ((List.range 128).map fun k => .n ((val% «verify_sig_lean_sphincs» "bits0[0]") + k)))),
    .hint (.bits (.n (val% «verify_sig_lean_sphincs» "d0[1]")) 0 128 (.stack ((List.range 128).map fun k => .n ((val% «verify_sig_lean_sphincs» "bits1[0]") + k)))),
    .hint (.bits (.n (val% «verify_sig_lean_sphincs» "d1[0]")) 0 16 (.stack ((List.range 16).map fun k => .n ((val% «verify_sig_lean_sphincs» "bits2[0]") + k))))]

/-- **`verify_sig_lean_sphincs`'s computed hints are the bit hints**: every other is pinned by the next atom (it has
none). -/
theorem sPinned : Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ sBitsAtoms)) pinsInverse
    (Fn.«verify_sig_lean_sphincs».core).body = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
