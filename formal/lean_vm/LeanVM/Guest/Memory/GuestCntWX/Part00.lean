module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_0 : kuxStaticRange 0 11 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_11 : kuxStaticRange 11 7 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_18 : kuxStaticRange 18 30 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
