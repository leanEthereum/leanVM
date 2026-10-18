module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_711 : WfRange 711 25 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_736 : WfRange 736 25 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_761 : WfRange 761 25 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_786 : WfRange 786 25 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
