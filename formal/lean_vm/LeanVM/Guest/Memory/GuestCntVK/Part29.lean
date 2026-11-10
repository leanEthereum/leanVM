module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_779 : kvkStaticRange 779 19 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_798 : kvkStaticRange 798 17 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
