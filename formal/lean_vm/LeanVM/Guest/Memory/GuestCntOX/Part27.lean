module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_925 : kwoxStaticRange 925 28 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_953 : kwoxStaticRange 953 21 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
