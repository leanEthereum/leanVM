module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1724 : kvdStaticRange 1724 9 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1733 : kvdStaticRange 1733 11 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1744 : kvdStaticRange 1744 8 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
