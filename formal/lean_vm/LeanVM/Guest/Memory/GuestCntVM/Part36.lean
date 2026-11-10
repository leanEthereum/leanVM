module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1048 : kvmStaticRange 1048 7 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
