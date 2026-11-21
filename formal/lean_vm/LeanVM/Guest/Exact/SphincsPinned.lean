/-
  LeanVM.Guest.Exact.SphincsPinned

  `verify_sig_lean_sphincs`'s computed hints are its three bit hints of `H_msg`'s cells (`Sig.sBitsAtoms`), by the
  kernel.
-/

module

public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.Pack.verify_sig_lean_sphincs.Core

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **The bit hints of `H_msg`'s cells** (`sBitsHint`'s atoms): `n17`'s and `n18`'s 128 bits, `n27`'s low 16. -/
def sBitsAtoms : List Atom :=
  [.hint (.bits (.n 17) 0 128 (.stack ((List.range 128).map fun k => .n (28 + k)))),
    .hint (.bits (.n 18) 0 128 (.stack ((List.range 128).map fun k => .n (156 + k)))),
    .hint (.bits (.n 27) 0 16 (.stack ((List.range 16).map fun k => .n (284 + k))))]

/-- **`verify_sig_lean_sphincs`'s computed hints are the bit hints**: every other is pinned by the next atom (it has
none). -/
theorem sPinned : Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ sBitsAtoms)) pinsInverse
    (Fn.«verify_sig_lean_sphincs».core).body = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
