module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_742 : kvmStaticRange 742 17 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_759 : kvmStaticRange 759 19 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
