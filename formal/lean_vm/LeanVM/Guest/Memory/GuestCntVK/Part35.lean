module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1015 : kvkStaticRange 1015 10 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1025 : kvkStaticRange 1025 13 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1038 : kvkStaticRange 1038 9 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
