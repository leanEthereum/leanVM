module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1020 : kvmStaticRange 1020 8 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1028 : kvmStaticRange 1028 7 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
