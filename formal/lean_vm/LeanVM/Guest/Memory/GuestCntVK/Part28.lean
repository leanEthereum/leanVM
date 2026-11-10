module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_755 : kvkStaticRange 755 14 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_769 : kvkStaticRange 769 17 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
