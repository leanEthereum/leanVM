module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_894 : kwoxStaticRange 894 14 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_908 : kwoxStaticRange 908 17 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
