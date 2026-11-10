module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1015 : kvxStaticRange 1015 10 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1025 : kvxStaticRange 1025 13 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1038 : kvxStaticRange 1038 9 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
