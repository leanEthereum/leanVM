module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_556 : kvkStaticRange 556 18 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_574 : kvkStaticRange 574 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
