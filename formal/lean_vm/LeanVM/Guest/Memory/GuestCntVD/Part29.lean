module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_913 : kvdStaticRange 913 12 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_925 : kvdStaticRange 925 11 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
