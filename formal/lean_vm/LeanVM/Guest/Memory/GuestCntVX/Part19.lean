module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1397 : kvxStaticRange 1397 18 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1415 : kvxStaticRange 1415 18 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
