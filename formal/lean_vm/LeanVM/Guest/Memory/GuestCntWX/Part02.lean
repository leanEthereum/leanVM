module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_289 : kuxStaticRange 289 20 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_309 : kuxStaticRange 309 3 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
