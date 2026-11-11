module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1556 : kvmStaticRange 1556 13 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1569 : kvmStaticRange 1569 12 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
