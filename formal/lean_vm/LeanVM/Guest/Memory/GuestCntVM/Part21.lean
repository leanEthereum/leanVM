module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_592 : kvmStaticRange 592 18 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_610 : kvmStaticRange 610 18 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
