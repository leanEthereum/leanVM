module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_576 : kvmStaticRange 576 19 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_595 : kvmStaticRange 595 18 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
