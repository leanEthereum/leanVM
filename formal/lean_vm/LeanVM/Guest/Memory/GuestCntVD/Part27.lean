module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_721 : kvdStaticRange 721 17 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_738 : kvdStaticRange 738 17 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
