module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1707 : kvxStaticRange 1707 13 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1720 : kvxStaticRange 1720 15 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
