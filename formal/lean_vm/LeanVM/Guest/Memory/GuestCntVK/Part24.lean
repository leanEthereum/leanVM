module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_711 : kvkStaticRange 711 17 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_728 : kvkStaticRange 728 17 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
