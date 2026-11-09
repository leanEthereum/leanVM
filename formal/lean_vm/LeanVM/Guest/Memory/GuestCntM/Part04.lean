module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_307 : kwmStaticRange 307 7 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_314 : kwmStaticRange 314 7 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
