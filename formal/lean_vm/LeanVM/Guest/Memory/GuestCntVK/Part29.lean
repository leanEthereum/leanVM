module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_786 : kvkStaticRange 786 18 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_804 : kvkStaticRange 804 17 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
