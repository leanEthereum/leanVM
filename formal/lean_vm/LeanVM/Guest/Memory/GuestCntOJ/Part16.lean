module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_602 : kwojStaticRange 602 16 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_618 : kwojStaticRange 618 16 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
