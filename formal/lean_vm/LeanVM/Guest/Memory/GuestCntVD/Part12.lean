module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1645 : kvdStaticRange 1645 16 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1661 : kvdStaticRange 1661 13 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
