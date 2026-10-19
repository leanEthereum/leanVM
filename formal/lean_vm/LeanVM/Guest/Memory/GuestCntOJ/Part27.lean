module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_925 : kwojStaticRange 925 28 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_953 : kwojStaticRange 953 21 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
