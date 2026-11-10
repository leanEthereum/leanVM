module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_354 : kuxStaticRange 354 30 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_384 : kuxStaticRange 384 30 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_414 : kuxStaticRange 414 30 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_444 : kuxStaticRange 444 30 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_474 : kuxStaticRange 474 30 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_504 : kuxStaticRange 504 30 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_534 : kuxStaticRange 534 30 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
