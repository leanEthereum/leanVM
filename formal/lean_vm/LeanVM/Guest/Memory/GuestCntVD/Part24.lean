module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_694 : kvdStaticRange 694 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_712 : kvdStaticRange 712 18 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
