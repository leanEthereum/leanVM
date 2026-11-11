module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_711 : kvmStaticRange 711 17 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_728 : kvmStaticRange 728 17 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
