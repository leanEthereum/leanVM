module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_711 : kvdStaticRange 711 17 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_728 : kvdStaticRange 728 17 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
