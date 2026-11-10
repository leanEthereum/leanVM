module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1735 : kvkStaticRange 1735 12 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1747 : kvkStaticRange 1747 12 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
