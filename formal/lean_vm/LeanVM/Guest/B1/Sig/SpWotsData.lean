/-
  LeanVM.Guest.B1.Sig.SpWotsData

  `sp_wots` in the guest's core IR is the template `spBody`.
-/

module

public import LeanVM.Guest.Data.Core04
public import LeanVM.Guest.B1.Sig.SpWotsLayout
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Sig.SpWotsData0
import LeanVM.Guest.B1.Sig.SpWotsData1

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`sp_wots`'s body is the template**, renumbered as the guest numbers it, checked by the kernel
in slices: the copies and powers, each digit group's dispatch, the checks and the leaf. -/
theorem spBody_eq : Data.core19.body = spBody := by
  have h127 := spBody_drop_127
  have h122 := drop_eq_of_take spBody_slice_122 h127
  have h117 := drop_eq_of_take spBody_slice_117 h122
  have h112 := drop_eq_of_take spBody_slice_112 h117
  have h107 := drop_eq_of_take spBody_slice_107 h112
  have h102 := drop_eq_of_take spBody_slice_102 h107
  have h97 := drop_eq_of_take spBody_slice_97 h102
  have h92 := drop_eq_of_take spBody_slice_92 h97
  have h87 := drop_eq_of_take spBody_slice_87 h92
  have h82 := drop_eq_of_take spBody_slice_82 h87
  have h77 := drop_eq_of_take spBody_slice_77 h82
  have h72 := drop_eq_of_take spBody_slice_72 h77
  have h67 := drop_eq_of_take spBody_slice_67 h72
  have h62 := drop_eq_of_take spBody_slice_62 h67
  have h57 := drop_eq_of_take spBody_slice_57 h62
  have h52 := drop_eq_of_take spBody_slice_52 h57
  have h47 := drop_eq_of_take spBody_slice_47 h52
  have h42 := drop_eq_of_take spBody_slice_42 h47
  have h37 := drop_eq_of_take spBody_slice_37 h42
  have h32 := drop_eq_of_take spBody_slice_32 h37
  have h27 := drop_eq_of_take spBody_slice_27 h32
  have h22 := drop_eq_of_take spBody_slice_22 h27
  have h12 := drop_eq_of_take spBody_slice_12 h22
  have h0 := drop_eq_of_take spBody_slice_0 h12
  rwa [List.drop_zero, List.drop_zero] at h0

end
end LeanVM.Guest.B1.Sig
