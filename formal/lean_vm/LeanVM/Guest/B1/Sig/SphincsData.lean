/-
  LeanVM.Guest.B1.Sig.SphincsData

  `verify_sig_lean_sphincs` and the 256 `sp_forest_key` specializations in the guest's core IR are
  the templates `sBody` and `fkBody`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.Template
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem sBody_eq : Data.core17.body = sBody := by decide +kernel

/-- `verify_sig_lean_sphincs` is the template. -/
theorem find_verify_sig_lean_sphincs :
    coreProgram.find? "verify_sig_lean_sphincs" = some ⟨"verify_sig_lean_sphincs", [.n 0], sBody⟩ := by
  rw [Program.find?_of_indexOf? (j := 17) (by decide +kernel) rfl, ← sBody_eq]
  rfl

/-- The function of forest key `t`. -/
def fkFn (t : Nat) : Fn := ⟨fkNames.getD t "", [.n 0, .n 1], fkBody t⟩

open scoped Dec in
theorem fk_data : ∀ t < 256, (coreProgram[205 + t]?).map (fun f => (f.name, f.params, f.body)) =
    some ((fkFn t).name, (fkFn t).params, (fkFn t).body) := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
