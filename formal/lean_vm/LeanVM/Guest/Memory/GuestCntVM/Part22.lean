module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_628 : kvmStaticRange 628 16 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_644 : kvmStaticRange 644 17 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
