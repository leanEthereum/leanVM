module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_808 : kvdStaticRange 808 13 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_821 : kvdStaticRange 821 17 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
