module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_342 : kuxStaticRange 342 6 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_348 : kuxStaticRange 348 6 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
