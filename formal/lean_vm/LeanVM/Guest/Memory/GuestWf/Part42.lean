module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_545 : WfRange 545 1 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
