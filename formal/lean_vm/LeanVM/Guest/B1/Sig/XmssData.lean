/-
  LeanVM.Guest.B1.Sig.XmssData

  `verify_lean_xmss` in the guest's core IR is the template `xBody`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.Template
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem xBody_eq : Data.core16.body = xBody := by decide +kernel

/-- `verify_lean_xmss` is the template. -/
theorem find_verify_lean_xmss :
    coreProgram.find? "verify_lean_xmss" = some ⟨"verify_lean_xmss", [.n 0], xBody⟩ := by
  rw [Program.find?_of_indexOf? (j := 16) (by decide +kernel) rfl, ← xBody_eq]
  rfl

end
end LeanVM.Guest.B1.Sig
