module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_345 : kvdStaticRange 345 2 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_347 : kvdStaticRange 347 1 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
