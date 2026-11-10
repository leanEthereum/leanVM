module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_653 : kvmStaticRange 653 17 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_670 : kvmStaticRange 670 18 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
