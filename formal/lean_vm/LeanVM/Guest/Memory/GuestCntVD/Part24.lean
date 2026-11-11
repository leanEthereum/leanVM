module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_712 : kvdStaticRange 712 17 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_729 : kvdStaticRange 729 13 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
