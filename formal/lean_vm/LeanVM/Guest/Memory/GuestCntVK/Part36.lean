module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1047 : kvkStaticRange 1047 7 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1054 : kvkStaticRange 1054 1 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
