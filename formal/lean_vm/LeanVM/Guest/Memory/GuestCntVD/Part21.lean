module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_592 : kvdStaticRange 592 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_610 : kvdStaticRange 610 18 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
