module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1201 : kvmStaticRange 1201 11 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1212 : kvmStaticRange 1212 15 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
