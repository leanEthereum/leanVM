module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_576 : kvkStaticRange 576 19 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_595 : kvkStaticRange 595 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
