module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_602 : kwoxStaticRange 602 16 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_618 : kwoxStaticRange 618 16 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
