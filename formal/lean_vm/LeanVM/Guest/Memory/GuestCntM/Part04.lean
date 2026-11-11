module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_313 : kwmStaticRange 313 3 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_316 : kwmStaticRange 316 3 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
