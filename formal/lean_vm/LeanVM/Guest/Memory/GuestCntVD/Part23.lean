module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_677 : kvdStaticRange 677 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_695 : kvdStaticRange 695 16 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
