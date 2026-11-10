module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_815 : kvkStaticRange 815 16 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_831 : kvkStaticRange 831 17 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
