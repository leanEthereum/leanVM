module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_866 : kwoxStaticRange 866 14 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_880 : kwoxStaticRange 880 14 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
