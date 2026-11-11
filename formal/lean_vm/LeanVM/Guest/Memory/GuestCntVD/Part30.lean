module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_959 : kvdStaticRange 959 13 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_972 : kvdStaticRange 972 14 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
