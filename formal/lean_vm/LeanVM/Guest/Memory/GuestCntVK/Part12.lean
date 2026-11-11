module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1201 : kvkStaticRange 1201 11 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1212 : kvkStaticRange 1212 15 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
