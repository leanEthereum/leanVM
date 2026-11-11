module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1016 : kvkStaticRange 1016 9 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1025 : kvkStaticRange 1025 8 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1033 : kvkStaticRange 1033 4 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
