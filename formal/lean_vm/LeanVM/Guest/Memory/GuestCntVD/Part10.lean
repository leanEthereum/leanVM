module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1119 : kvdStaticRange 1119 14 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1133 : kvdStaticRange 1133 18 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
