module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_980 : kvdStaticRange 980 13 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_993 : kvdStaticRange 993 11 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1004 : kvdStaticRange 1004 12 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
