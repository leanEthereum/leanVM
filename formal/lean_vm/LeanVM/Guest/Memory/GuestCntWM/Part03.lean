module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_316 : kumStaticRange 316 3 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_319 : kumStaticRange 319 2 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
