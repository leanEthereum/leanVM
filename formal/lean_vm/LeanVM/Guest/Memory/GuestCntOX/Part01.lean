module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_14 : kwoxStaticRange 14 1 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
