module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1311 : kvdStaticRange 1311 20 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1331 : kvdStaticRange 1331 12 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
