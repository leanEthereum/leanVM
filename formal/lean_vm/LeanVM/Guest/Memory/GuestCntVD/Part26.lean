module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_778 : kvdStaticRange 778 12 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_790 : kvdStaticRange 790 18 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
