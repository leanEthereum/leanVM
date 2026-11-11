module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1373 : kvmStaticRange 1373 14 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1387 : kvmStaticRange 1387 10 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
