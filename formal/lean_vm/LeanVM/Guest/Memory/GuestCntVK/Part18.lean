module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_461 : kvkStaticRange 461 21 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_482 : kvkStaticRange 482 20 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_502 : kvkStaticRange 502 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
