module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1257 : kvmStaticRange 1257 14 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1271 : kvmStaticRange 1271 21 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
