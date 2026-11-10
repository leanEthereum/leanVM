module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1707 : kvmStaticRange 1707 13 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1720 : kvmStaticRange 1720 15 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
