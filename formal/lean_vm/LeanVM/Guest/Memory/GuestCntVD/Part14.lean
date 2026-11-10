module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1735 : kvdStaticRange 1735 12 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1747 : kvdStaticRange 1747 12 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
