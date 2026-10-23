module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_664 : kwoxStaticRange 664 15 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_679 : kwoxStaticRange 679 15 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
