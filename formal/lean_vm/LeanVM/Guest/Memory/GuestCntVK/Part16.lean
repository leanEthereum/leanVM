module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1311 : kvkStaticRange 1311 20 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1331 : kvkStaticRange 1331 12 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
