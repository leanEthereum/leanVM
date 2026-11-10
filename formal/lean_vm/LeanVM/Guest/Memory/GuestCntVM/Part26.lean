module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_683 : kvmStaticRange 683 17 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_700 : kvmStaticRange 700 18 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
