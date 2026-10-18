module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_141 : WfRange 141 38 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_179 : WfRange 179 2 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_181 : WfRange 181 2 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_183 : WfRange 183 2 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_185 : WfRange 185 2 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
