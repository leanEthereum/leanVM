module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_755 : kvmStaticRange 755 14 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_769 : kvmStaticRange 769 17 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
