module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_810 : kwoxStaticRange 810 14 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_824 : kwoxStaticRange 824 14 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
