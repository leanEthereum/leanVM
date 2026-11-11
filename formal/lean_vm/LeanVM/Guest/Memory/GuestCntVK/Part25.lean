module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_742 : kvkStaticRange 742 17 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_759 : kvkStaticRange 759 19 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
