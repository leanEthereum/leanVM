module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_724 : kwojStaticRange 724 15 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_739 : kwojStaticRange 739 15 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
