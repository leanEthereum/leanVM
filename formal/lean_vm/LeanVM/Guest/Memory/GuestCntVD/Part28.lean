module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_883 : kvdStaticRange 883 15 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_898 : kvdStaticRange 898 15 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
