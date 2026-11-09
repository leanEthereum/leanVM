/-
  LeanVM.Guest.B1.Sig.SpWotsData0

  `sp_wots` in the guest's core IR agrees with the template `spBody` on the copies, the powers and digit groups 0 to 10 (statements 0 to 71).
-/

module

public import LeanVM.Guest.Data.Core04
public import LeanVM.Guest.B1.Sig.SpWotsLayout
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem spBody_slice_0 : (Data.core19.body.drop 0).take 12 = (spBody.drop 0).take 12 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_12 : (Data.core19.body.drop 12).take 10 = (spBody.drop 12).take 10 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_22 : (Data.core19.body.drop 22).take 5 = (spBody.drop 22).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_27 : (Data.core19.body.drop 27).take 5 = (spBody.drop 27).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_32 : (Data.core19.body.drop 32).take 5 = (spBody.drop 32).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_37 : (Data.core19.body.drop 37).take 5 = (spBody.drop 37).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_42 : (Data.core19.body.drop 42).take 5 = (spBody.drop 42).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_47 : (Data.core19.body.drop 47).take 5 = (spBody.drop 47).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_52 : (Data.core19.body.drop 52).take 5 = (spBody.drop 52).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_57 : (Data.core19.body.drop 57).take 5 = (spBody.drop 57).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_62 : (Data.core19.body.drop 62).take 5 = (spBody.drop 62).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_67 : (Data.core19.body.drop 67).take 5 = (spBody.drop 67).take 5 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
