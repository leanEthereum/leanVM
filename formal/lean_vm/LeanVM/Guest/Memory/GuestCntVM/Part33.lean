module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_968 : kvmStaticRange 968 12 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_980 : kvmStaticRange 980 11 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
