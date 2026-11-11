module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_288 : kuxStaticRange 288 25 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_313 : kuxStaticRange 313 3 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
