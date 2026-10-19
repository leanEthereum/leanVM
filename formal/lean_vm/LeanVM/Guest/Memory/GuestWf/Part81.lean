module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_1011 : WfRange 1011 9 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
