module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_345 : kvkStaticRange 345 2 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_347 : kvkStaticRange 347 1 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
