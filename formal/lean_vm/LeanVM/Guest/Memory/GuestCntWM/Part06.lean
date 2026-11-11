module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_987 : kumStaticRange 987 30 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_1017 : kumStaticRange 1017 20 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
