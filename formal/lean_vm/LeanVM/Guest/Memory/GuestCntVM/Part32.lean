module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_939 : kvmStaticRange 939 15 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_954 : kvmStaticRange 954 14 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
