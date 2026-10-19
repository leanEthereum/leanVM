module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_17 : kwoxStaticRange 17 1 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
