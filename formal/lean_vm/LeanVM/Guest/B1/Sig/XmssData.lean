/-
  LeanVM.Guest.B1.Sig.XmssData

  `verify_lean_xmss` in the guest's core IR is the template `xBody`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.Template
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Sig.XmssData0
import LeanVM.Guest.B1.Sig.XmssData1
import LeanVM.Guest.B1.Sig.XmssData2
import LeanVM.Guest.B1.Sig.XmssData3
import LeanVM.Guest.B1.Sig.XmssData4
import LeanVM.Guest.B1.Sig.XmssData5
import LeanVM.Guest.B1.Sig.XmssData6
import LeanVM.Guest.B1.Sig.XmssData7

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- Two lists agreeing on a slice from `a` and from its end on agree from `a`. -/
theorem drop_eq_of_take {α : Type} {l r : List α} {a n : Nat} (ht : (l.drop a).take n = (r.drop a).take n)
    (hd : l.drop (a + n) = r.drop (a + n)) : l.drop a = r.drop a := by
  rw [← List.take_append_drop n (l.drop a), ← List.take_append_drop n (r.drop a), ht, List.drop_drop,
    List.drop_drop, hd]

/-- The body, checked by the kernel in slices (`XmssData0` to `XmssData7`). -/
theorem xBody_eq : Data.core16.body = xBody := by
  have h512 := xBody_drop_512
  have h492 := drop_eq_of_take xBody_slice_492 h512
  have h472 := drop_eq_of_take xBody_slice_472 h492
  have h450 := drop_eq_of_take xBody_slice_450 h472
  have h220 := drop_eq_of_take xBody_slice_220 h450
  have h200 := drop_eq_of_take xBody_slice_200 h220
  have h180 := drop_eq_of_take xBody_slice_180 h200
  have h0 := drop_eq_of_take xBody_slice_0 h180
  rwa [List.drop_zero, List.drop_zero] at h0

/-- `verify_lean_xmss` is the template. -/
theorem find_verify_lean_xmss :
    coreProgram.find? "verify_lean_xmss" = some ⟨"verify_lean_xmss", [.n 0], xBody⟩ := by
  rw [Program.find?_of_indexOf? (j := 16) (by decide +kernel) rfl, ← xBody_eq]
  rfl

end
end LeanVM.Guest.B1.Sig
