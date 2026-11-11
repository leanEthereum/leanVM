module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_612 : kvkStaticRange 612 14 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_626 : kvkStaticRange 626 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
