module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1311 : kvmStaticRange 1311 20 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1331 : kvmStaticRange 1331 12 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
