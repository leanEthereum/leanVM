module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_576 : kvdStaticRange 576 19 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_595 : kvdStaticRange 595 18 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
