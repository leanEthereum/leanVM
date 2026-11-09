module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_766 : kvdStaticRange 766 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_784 : kvdStaticRange 784 20 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_804 : kvdStaticRange 804 24 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_828 : kvdStaticRange 828 22 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
