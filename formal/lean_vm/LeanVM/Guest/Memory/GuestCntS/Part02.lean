module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_36 : kwsStaticRange 36 1 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
