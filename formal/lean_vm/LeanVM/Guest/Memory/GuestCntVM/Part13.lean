module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1227 : kvmStaticRange 1227 19 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_1246 : kvmStaticRange 1246 11 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
