module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_607 : WfRange 607 29 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_636 : WfRange 636 25 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_661 : WfRange 661 25 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_686 : WfRange 686 25 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
