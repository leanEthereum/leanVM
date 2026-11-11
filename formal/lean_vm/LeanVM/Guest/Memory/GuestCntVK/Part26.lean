module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_779 : kvkStaticRange 779 18 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_797 : kvkStaticRange 797 16 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
