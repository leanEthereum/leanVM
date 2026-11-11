module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1479 : kvmStaticRange 1479 12 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1491 : kvmStaticRange 1491 12 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
