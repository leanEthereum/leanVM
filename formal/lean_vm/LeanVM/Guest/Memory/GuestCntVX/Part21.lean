module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1452 : kvxStaticRange 1452 19 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1471 : kvxStaticRange 1471 12 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
