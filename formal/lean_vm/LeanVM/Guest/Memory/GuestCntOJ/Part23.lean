module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_810 : kwojStaticRange 810 14 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_824 : kwojStaticRange 824 14 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
