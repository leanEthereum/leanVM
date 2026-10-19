module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_548 : WfRange 548 12 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
