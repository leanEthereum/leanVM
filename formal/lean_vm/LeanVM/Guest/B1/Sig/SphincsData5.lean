/-
  LeanVM.Guest.B1.Sig.SphincsData5

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sBody` on from
  statement 817 on.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.Template
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem sBody_drop_817 : Data.core17.body.drop 817 = sBody.drop 817 := by decide +kernel

end
end LeanVM.Guest.B1.Sig
