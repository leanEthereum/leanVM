module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1759 : kvmStaticRange 1759 12 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1771 : kvmStaticRange 1771 11 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
