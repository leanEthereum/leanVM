module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_954 : kvmStaticRange 954 12 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_966 : kvmStaticRange 966 14 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
