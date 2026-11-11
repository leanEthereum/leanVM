module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_959 : kvmStaticRange 959 13 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_972 : kvmStaticRange 972 14 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
