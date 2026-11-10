module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1782 : kvdStaticRange 1782 11 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1793 : kvdStaticRange 1793 10 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
