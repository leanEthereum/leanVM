module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_754 : kwojStaticRange 754 14 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_768 : kwojStaticRange 768 14 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
