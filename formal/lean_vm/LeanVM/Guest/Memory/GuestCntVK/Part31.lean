module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_980 : kvkStaticRange 980 13 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_993 : kvkStaticRange 993 11 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1004 : kvkStaticRange 1004 12 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
