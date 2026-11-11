module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1530 : kvxStaticRange 1530 13 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1543 : kvxStaticRange 1543 13 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
