module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_344 : kumStaticRange 344 6 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_350 : kumStaticRange 350 7 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
