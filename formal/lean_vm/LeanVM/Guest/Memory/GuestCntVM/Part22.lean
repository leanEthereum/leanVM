module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1483 : kvmStaticRange 1483 8 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1491 : kvmStaticRange 1491 11 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
