module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_987 : kvkStaticRange 987 15 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1002 : kvkStaticRange 1002 13 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
