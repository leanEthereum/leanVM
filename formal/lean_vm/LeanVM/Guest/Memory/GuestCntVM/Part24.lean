module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1530 : kvmStaticRange 1530 13 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1543 : kvmStaticRange 1543 13 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
