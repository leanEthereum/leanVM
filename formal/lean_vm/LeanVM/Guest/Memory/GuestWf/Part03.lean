module

public import LeanVM.Guest.Memory.GuestWf.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem wfRange_187 : WfRange 187 2 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_189 : WfRange 189 2 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_191 : WfRange 191 2 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_193 : WfRange 193 2 := by
  unfold WfRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wfRange_195 : WfRange 195 2 := by
  unfold WfRange; decide +kernel

end
end LeanVM.Guest
