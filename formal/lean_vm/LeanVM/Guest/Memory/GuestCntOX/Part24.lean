module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_838 : kwoxStaticRange 838 14 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_852 : kwoxStaticRange 852 14 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
