module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_612 : kvmStaticRange 612 14 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_626 : kvmStaticRange 626 18 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
