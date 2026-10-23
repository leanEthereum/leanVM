module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_866 : kwojStaticRange 866 14 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_880 : kwojStaticRange 880 14 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
