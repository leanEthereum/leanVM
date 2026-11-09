module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_972 : kvdStaticRange 972 9 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_981 : kvdStaticRange 981 7 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_988 : kvdStaticRange 988 3 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
