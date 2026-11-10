module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_0 : kvmStaticRange 0 11 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_11 : kvmStaticRange 11 7 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
