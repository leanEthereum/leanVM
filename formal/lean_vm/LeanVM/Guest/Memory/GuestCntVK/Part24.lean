module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_613 : kvkStaticRange 613 19 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_632 : kvkStaticRange 632 17 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
