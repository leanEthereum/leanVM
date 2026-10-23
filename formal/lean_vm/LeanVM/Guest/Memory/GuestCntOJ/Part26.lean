module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_894 : kwojStaticRange 894 14 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_908 : kwojStaticRange 908 17 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
