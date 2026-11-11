module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_959 : kvkStaticRange 959 13 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_972 : kvkStaticRange 972 14 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
