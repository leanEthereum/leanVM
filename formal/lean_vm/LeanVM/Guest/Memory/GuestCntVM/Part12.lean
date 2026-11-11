module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1645 : kvmStaticRange 1645 16 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1661 : kvmStaticRange 1661 13 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
