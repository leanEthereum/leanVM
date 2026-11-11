module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_813 : kvdStaticRange 813 17 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_830 : kvdStaticRange 830 16 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
