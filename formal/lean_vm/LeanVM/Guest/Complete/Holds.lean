module

public import LeanVM.Guest.Complete.Left
public import LeanVM.Guest.EndExecOffNil

/-!
# The guest's execution completeness, at the deployed choices

`guestExecutionComplete_of_routed`: `GuestExecutionComplete` once every compiled function of the
guest is on the core route (`CoreMode.offSigs = []`, the generated list of the functions off it):
`guestExecutionComplete_of_left` with `GuestLeft.off` from `off_of_routed`.
-/

namespace LeanVM.Guest.Complete

public section

/-- **`GuestExecutionComplete` once every function is on the core route.** -/
theorem guestExecutionComplete_of_routed (h : CoreMode.offSigs = []) :
    LeanVM.Guest.Completeness.GuestExecutionComplete :=
  guestExecutionComplete_of_left ⟨off_of_routed h⟩

end

end LeanVM.Guest.Complete
