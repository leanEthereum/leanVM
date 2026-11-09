module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_520 : kvdStaticRange 520 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_538 : kvdStaticRange 538 18 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
