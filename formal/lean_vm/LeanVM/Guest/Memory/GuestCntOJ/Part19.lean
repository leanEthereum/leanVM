module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_694 : kwojStaticRange 694 15 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_709 : kwojStaticRange 709 15 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
