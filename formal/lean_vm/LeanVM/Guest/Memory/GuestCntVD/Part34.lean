module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_987 : kvdStaticRange 987 15 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1002 : kvdStaticRange 1002 13 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
