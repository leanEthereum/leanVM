module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1119 : kvmStaticRange 1119 14 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1133 : kvmStaticRange 1133 18 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
