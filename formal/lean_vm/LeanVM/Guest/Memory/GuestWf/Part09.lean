module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_911 : WfRange 911 23 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_934 : WfRange 934 25 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_959 : WfRange 959 32 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_991 : WfRange 991 29 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
