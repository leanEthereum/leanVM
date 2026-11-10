module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_649 : kvmStaticRange 649 17 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_666 : kvmStaticRange 666 17 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
