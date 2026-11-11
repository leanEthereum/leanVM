module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1227 : kvdStaticRange 1227 19 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1246 : kvdStaticRange 1246 11 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
