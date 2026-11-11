module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1556 : kvxStaticRange 1556 13 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1569 : kvxStaticRange 1569 12 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
