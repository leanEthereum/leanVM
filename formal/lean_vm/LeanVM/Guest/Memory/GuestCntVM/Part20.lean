module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_574 : kvmStaticRange 574 19 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_593 : kvmStaticRange 593 19 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
