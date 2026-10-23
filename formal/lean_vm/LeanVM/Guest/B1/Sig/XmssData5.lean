/-
  LeanVM.Guest.B1.Sig.XmssData5

  `verify_lean_xmss` in the guest's core IR agrees with the template `xBody` on statements 472 to
  491.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.Template
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem xBody_slice_472 : (Data.core16.body.drop 472).take 20 = (xBody.drop 472).take 20 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
