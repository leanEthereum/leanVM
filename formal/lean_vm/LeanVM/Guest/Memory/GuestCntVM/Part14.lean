module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1735 : kvmStaticRange 1735 12 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1747 : kvmStaticRange 1747 12 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
