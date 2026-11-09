module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_351 : kvkStaticRange 351 22 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_373 : kvkStaticRange 373 23 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_396 : kvkStaticRange 396 14 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_410 : kvkStaticRange 410 30 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_440 : kvkStaticRange 440 21 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
