module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_351 : kvxStaticRange 351 22 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_373 : kvxStaticRange 373 23 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_396 : kvxStaticRange 396 14 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_410 : kvxStaticRange 410 30 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_440 : kvxStaticRange 440 21 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
