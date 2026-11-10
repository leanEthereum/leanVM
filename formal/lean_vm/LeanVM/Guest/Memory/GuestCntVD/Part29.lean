module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_779 : kvdStaticRange 779 19 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_798 : kvdStaticRange 798 17 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
