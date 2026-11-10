module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_961 : kvkStaticRange 961 14 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_975 : kvkStaticRange 975 12 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
