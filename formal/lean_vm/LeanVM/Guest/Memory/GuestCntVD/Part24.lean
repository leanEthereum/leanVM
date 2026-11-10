module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_613 : kvdStaticRange 613 19 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_632 : kvdStaticRange 632 17 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
