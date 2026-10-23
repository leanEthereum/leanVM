module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_664 : kwojStaticRange 664 15 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_679 : kwojStaticRange 679 15 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
