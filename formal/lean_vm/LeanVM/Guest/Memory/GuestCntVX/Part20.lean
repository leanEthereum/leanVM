module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1433 : kvxStaticRange 1433 8 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1441 : kvxStaticRange 1441 11 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
