/-
  LeanVM.Guest.B1.Sig.XmssData7

  `verify_lean_xmss` in the guest's core IR agrees with the template `xBody` on from statement 512
  on.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.Template
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem xBody_drop_512 : Data.core16.body.drop 512 = xBody.drop 512 := by decide +kernel

end
end LeanVM.Guest.B1.Sig
