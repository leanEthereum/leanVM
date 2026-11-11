module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_677 : kvmStaticRange 677 18 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_695 : kvmStaticRange 695 17 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
