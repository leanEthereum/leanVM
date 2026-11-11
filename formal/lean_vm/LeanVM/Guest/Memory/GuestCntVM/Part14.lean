module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1700 : kvmStaticRange 1700 12 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1712 : kvmStaticRange 1712 12 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
