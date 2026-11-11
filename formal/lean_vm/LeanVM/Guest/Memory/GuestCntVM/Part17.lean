module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1343 : kvmStaticRange 1343 11 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1354 : kvmStaticRange 1354 19 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
