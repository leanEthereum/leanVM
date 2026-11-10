module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_718 : kvdStaticRange 718 13 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_731 : kvdStaticRange 731 17 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
