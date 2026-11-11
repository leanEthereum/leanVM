/-
  LeanVM.Guest.B1.Place.OsPlaced

  open_stacked is complete placed at every stack size and rate: the statements the guest's
  completeness consumes.
-/

module

public import LeanVM.Guest.B1.Place.OsComplete
public import LeanVM.Guest.B1.Place.ValsProof

/-!
# `open_stacked`, placed

`open_stacked_completeAtD`, `open_stacked_completeAtB`: `open_stacked_completeAtD_of` and
`open_stacked_completeAtB_of` (`Place/OsComplete.lean`) at the honest valuation's values
(`os_call_vals`) and the dispatches on the rate's selector (`os_disp_rate`).
-/

namespace LeanVM.Guest.B1

@[expose] public section

/-- **`open_stacked` is complete placed at every stack log and rate.** -/
theorem open_stacked_completeAtD : open_stacked_completeAtD_Spec :=
  open_stacked_completeAtD_of os_call_vals os_disp_rate

/-- **`open_stacked` is complete placed within `osBosAt` words.** -/
theorem open_stacked_completeAtB : open_stacked_completeAtB_Spec :=
  open_stacked_completeAtB_of os_call_vals os_disp_rate

end
end LeanVM.Guest.B1
