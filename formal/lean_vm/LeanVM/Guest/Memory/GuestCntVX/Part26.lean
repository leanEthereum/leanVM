module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1581 : kvxStaticRange 1581 12 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1593 : kvxStaticRange 1593 8 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
