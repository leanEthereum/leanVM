module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1292 : kvmStaticRange 1292 8 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1300 : kvmStaticRange 1300 11 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
