module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1257 : kvdStaticRange 1257 14 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1271 : kvdStaticRange 1271 21 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
