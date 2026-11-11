module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1502 : kvmStaticRange 1502 12 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1514 : kvmStaticRange 1514 16 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
