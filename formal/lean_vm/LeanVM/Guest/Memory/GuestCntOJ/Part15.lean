module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_564 : kwojStaticRange 564 22 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_586 : kwojStaticRange 586 16 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
