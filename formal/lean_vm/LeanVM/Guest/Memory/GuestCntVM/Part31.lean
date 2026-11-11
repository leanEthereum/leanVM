module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_980 : kvmStaticRange 980 13 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_993 : kvmStaticRange 993 11 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1004 : kvmStaticRange 1004 12 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
