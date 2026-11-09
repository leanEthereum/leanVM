module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_628 : kvdStaticRange 628 16 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_644 : kvdStaticRange 644 17 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
