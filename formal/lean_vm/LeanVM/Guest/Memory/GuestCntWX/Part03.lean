module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_316 : kuxStaticRange 316 7 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_323 : kuxStaticRange 323 30 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_353 : kuxStaticRange 353 30 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
