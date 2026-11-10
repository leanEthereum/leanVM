module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1759 : kvdStaticRange 1759 12 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1771 : kvdStaticRange 1771 11 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
