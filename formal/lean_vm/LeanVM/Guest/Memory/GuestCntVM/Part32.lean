module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1016 : kvmStaticRange 1016 9 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1025 : kvmStaticRange 1025 8 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1033 : kvmStaticRange 1033 4 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
