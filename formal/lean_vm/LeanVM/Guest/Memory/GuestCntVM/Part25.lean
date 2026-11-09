module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_730 : kvmStaticRange 730 18 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_748 : kvmStaticRange 748 18 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
