module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1373 : kvxStaticRange 1373 14 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1387 : kvxStaticRange 1387 10 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
