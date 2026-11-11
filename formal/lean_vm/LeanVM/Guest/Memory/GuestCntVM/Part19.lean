module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1397 : kvmStaticRange 1397 18 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1415 : kvmStaticRange 1415 18 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
