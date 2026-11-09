module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_351 : kvmStaticRange 351 22 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_373 : kvmStaticRange 373 23 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_396 : kvmStaticRange 396 14 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_410 : kvmStaticRange 410 30 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_440 : kvmStaticRange 440 21 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
