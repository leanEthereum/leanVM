module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_520 : kvmStaticRange 520 18 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_538 : kvmStaticRange 538 18 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
