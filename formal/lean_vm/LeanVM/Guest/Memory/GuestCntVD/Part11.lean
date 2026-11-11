module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1448 : kvdStaticRange 1448 15 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1463 : kvdStaticRange 1463 16 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
