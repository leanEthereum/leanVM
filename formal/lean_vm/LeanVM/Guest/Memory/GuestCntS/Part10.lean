module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_1516 : kwsStaticRange 1516 19 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
