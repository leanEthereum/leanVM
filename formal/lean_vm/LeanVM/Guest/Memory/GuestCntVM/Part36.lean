module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1047 : kvmStaticRange 1047 7 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1054 : kvmStaticRange 1054 1 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
