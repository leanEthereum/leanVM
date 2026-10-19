module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_574 : WfRange 574 17 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
