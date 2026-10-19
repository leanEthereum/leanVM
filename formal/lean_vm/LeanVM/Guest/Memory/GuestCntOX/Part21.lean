module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_754 : kwoxStaticRange 754 14 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_768 : kwoxStaticRange 768 14 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
