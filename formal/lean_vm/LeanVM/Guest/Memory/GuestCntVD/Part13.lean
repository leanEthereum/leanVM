module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1503 : kvdStaticRange 1503 12 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1515 : kvdStaticRange 1515 10 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
