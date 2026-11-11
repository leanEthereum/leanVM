module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1581 : kvmStaticRange 1581 12 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1593 : kvmStaticRange 1593 8 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
