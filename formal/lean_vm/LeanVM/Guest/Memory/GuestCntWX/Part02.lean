module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_320 : kuxStaticRange 320 17 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_337 : kuxStaticRange 337 7 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
