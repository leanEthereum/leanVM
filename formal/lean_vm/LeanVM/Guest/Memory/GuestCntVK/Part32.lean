module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1020 : kvkStaticRange 1020 8 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1028 : kvkStaticRange 1028 7 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
