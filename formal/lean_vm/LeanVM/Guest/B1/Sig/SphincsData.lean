/-
  LeanVM.Guest.B1.Sig.SphincsData

  `verify_sig_lean_sphincs` in the guest's core IR is the template `sBody`.
-/

module

public import LeanVM.Guest.Pack.verify_sig_lean_sphincs.Core
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open LeanVM.Guest.KernelLit in
/-- **`verify_sig_lean_sphincs`'s body is the template**, checked by the kernel as one definitional
equality, which compares the two terms structurally and unfolds each side only as far as the
comparison needs. -/
kernel_rfl sBody_eq : (Fn.«verify_sig_lean_sphincs».core).body = sBody

end
end LeanVM.Guest.B1.Sig
