module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_694 : kwoxStaticRange 694 15 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_709 : kwoxStaticRange 709 15 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
