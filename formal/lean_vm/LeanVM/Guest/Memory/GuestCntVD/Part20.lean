module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_574 : kvdStaticRange 574 19 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_593 : kvdStaticRange 593 19 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
