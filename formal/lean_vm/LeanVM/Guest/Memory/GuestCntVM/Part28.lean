module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_883 : kvmStaticRange 883 15 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_898 : kvmStaticRange 898 15 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
