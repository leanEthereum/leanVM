module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_811 : WfRange 811 25 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_836 : WfRange 836 25 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_861 : WfRange 861 25 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_886 : WfRange 886 25 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
