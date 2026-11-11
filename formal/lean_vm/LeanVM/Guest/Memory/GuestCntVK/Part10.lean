module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1119 : kvkStaticRange 1119 14 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1133 : kvkStaticRange 1133 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
