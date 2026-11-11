module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_612 : kvdStaticRange 612 14 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_626 : kvdStaticRange 626 18 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
