module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1700 : kvxStaticRange 1700 12 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1712 : kvxStaticRange 1712 12 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
