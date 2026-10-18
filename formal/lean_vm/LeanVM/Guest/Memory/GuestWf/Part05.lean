module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_503 : WfRange 503 39 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_542 : WfRange 542 3 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_545 : WfRange 545 29 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_574 : WfRange 574 33 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
