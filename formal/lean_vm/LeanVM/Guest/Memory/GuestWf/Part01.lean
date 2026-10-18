module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_12 : WfRange 12 26 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_38 : WfRange 38 53 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_91 : WfRange 91 25 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_116 : WfRange 116 25 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
