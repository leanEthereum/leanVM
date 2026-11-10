module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_688 : kvmStaticRange 688 14 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_702 : kvmStaticRange 702 19 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
