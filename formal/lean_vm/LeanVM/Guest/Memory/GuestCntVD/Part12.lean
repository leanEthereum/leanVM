module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1201 : kvdStaticRange 1201 11 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1212 : kvdStaticRange 1212 15 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
