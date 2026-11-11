module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_343 : kumStaticRange 343 6 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_349 : kumStaticRange 349 6 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
