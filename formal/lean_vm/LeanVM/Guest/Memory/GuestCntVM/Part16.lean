module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1782 : kvmStaticRange 1782 11 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1793 : kvmStaticRange 1793 10 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
