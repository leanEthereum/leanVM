module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1452 : kvmStaticRange 1452 19 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1471 : kvmStaticRange 1471 12 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
