/-
  LeanVM.Guest.B1.Sig.XmssData3

  `verify_lean_xmss` in the guest's core IR agrees with the template `xBody` on statements 220 to
  449.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.Template
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem xBody_slice_220 : (Data.core16.body.drop 220).take 230 = (xBody.drop 220).take 230 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
