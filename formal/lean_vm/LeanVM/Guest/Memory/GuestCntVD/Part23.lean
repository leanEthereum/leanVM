module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_661 : kvdStaticRange 661 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_679 : kvdStaticRange 679 15 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
