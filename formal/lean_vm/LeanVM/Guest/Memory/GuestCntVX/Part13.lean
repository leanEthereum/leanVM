module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1503 : kvxStaticRange 1503 12 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1515 : kvxStaticRange 1515 10 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
