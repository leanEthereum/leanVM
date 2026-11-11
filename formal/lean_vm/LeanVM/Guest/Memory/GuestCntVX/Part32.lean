module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1016 : kvxStaticRange 1016 9 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1025 : kvxStaticRange 1025 8 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1033 : kvxStaticRange 1033 4 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
