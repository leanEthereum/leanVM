module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_745 : kvmStaticRange 745 15 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_760 : kvmStaticRange 760 19 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
