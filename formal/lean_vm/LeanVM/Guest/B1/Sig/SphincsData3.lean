/-
  LeanVM.Guest.B1.Sig.SphincsData3

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sBody` on statements
  777 to 796.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.Template
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem sBody_slice_777 : (Data.core17.body.drop 777).take 20 = (sBody.drop 777).take 20 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
