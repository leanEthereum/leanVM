module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_0 : kwoxStaticRange 0 11 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_11 : kwoxStaticRange 11 1 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_12 : kwoxStaticRange 12 2 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
