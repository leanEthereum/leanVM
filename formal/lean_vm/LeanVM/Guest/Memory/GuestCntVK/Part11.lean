module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1448 : kvkStaticRange 1448 15 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1463 : kvkStaticRange 1463 16 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
