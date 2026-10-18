module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_197 : WfRange 197 2 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_199 : WfRange 199 2 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_201 : WfRange 201 2 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_203 : WfRange 203 150 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_353 : WfRange 353 150 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
