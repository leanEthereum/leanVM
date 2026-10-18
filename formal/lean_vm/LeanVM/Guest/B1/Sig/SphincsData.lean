/-
  LeanVM.Guest.B1.Sig.SphincsData

  `verify_sig_lean_sphincs` and the 256 `sp_forest_key` specializations in the guest's core IR are
  the templates `sBody` and `fkBody`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.Template
public import LeanVM.Guest.B1.Sig.XmssData
import LeanVM.Guest.B1.Sig.SphincsData0
import LeanVM.Guest.B1.Sig.SphincsData1
import LeanVM.Guest.B1.Sig.SphincsData2
import LeanVM.Guest.B1.Sig.SphincsData3
import LeanVM.Guest.B1.Sig.SphincsData4
import LeanVM.Guest.B1.Sig.SphincsData5
import LeanVM.Guest.B1.Sig.SphincsFk0
import LeanVM.Guest.B1.Sig.SphincsFk1
import LeanVM.Guest.B1.Sig.SphincsFk2
import LeanVM.Guest.B1.Sig.SphincsFk3

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The body, checked by the kernel in slices (`SphincsData0` to `SphincsData5`). -/
theorem sBody_eq : Data.core17.body = sBody := by
  have h817 := sBody_drop_817
  have h797 := drop_eq_of_take sBody_slice_797 h817
  have h777 := drop_eq_of_take sBody_slice_777 h797
  have h757 := drop_eq_of_take sBody_slice_757 h777
  have h737 := drop_eq_of_take sBody_slice_737 h757
  have h0 := drop_eq_of_take sBody_slice_0 h737
  rwa [List.drop_zero, List.drop_zero] at h0

/-- `verify_sig_lean_sphincs` is the template. -/
theorem find_verify_sig_lean_sphincs :
    coreProgram.find? "verify_sig_lean_sphincs" = some ⟨"verify_sig_lean_sphincs", [.n 0], sBody⟩ := by
  rw [Program.find?_of_indexOf? (j := 17) (by decide +kernel) rfl, ← sBody_eq]
  rfl

/-- The forest keys, checked by the kernel in four ranges (`SphincsFk0` to `SphincsFk3`). -/
theorem fk_data : ∀ t < 256, (coreProgram[205 + t]?).map (fun f => (f.name, f.params, f.body)) =
    some ((fkFn t).name, (fkFn t).params, (fkFn t).body) ∧
    coreProgram.indexOf? (fkFn t).name = some (205 + t) := by
  intro t ht
  obtain ⟨k, hk, r, hr, rfl⟩ : ∃ k < 4, ∃ r < 64, t = 64 * k + r := ⟨t / 64, by omega, t % 64, by omega, by omega⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · simpa using And.intro (fk_data_0 r hr) (fk_index_0_all r hr)
  · simpa using And.intro (fk_data_64 r hr) (fk_index_64_all r hr)
  · simpa using And.intro (fk_data_128 r hr) (fk_index_128_all r hr)
  · simpa using And.intro (fk_data_192 r hr) (fk_index_192_all r hr)

end
end LeanVM.Guest.B1.Sig
