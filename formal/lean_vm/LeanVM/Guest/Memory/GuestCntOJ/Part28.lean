module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_974 : kwojStaticRange 974 11 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_985 : kwojStaticRange 985 11 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
