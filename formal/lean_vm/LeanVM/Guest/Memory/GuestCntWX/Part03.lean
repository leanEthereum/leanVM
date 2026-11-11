module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_344 : kuxStaticRange 344 6 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_350 : kuxStaticRange 350 7 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
