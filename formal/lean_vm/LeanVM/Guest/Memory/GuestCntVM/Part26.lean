module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_766 : kvmStaticRange 766 18 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_784 : kvmStaticRange 784 20 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_804 : kvmStaticRange 804 24 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_828 : kvmStaticRange 828 22 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
