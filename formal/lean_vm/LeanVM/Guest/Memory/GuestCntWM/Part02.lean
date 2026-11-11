module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_320 : kumStaticRange 320 18 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_338 : kumStaticRange 338 3 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
