module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_345 : kvmStaticRange 345 2 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_347 : kvmStaticRange 347 1 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
