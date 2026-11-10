module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_718 : kvmStaticRange 718 13 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_731 : kvmStaticRange 731 17 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
