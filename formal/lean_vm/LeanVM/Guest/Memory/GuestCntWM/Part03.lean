module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_342 : kumStaticRange 342 6 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_348 : kumStaticRange 348 6 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
