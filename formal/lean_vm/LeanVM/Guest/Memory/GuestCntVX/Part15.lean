module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1292 : kvxStaticRange 1292 8 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1300 : kvxStaticRange 1300 11 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
