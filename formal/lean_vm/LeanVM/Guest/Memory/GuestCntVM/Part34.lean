module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_987 : kvmStaticRange 987 15 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1002 : kvmStaticRange 1002 13 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
