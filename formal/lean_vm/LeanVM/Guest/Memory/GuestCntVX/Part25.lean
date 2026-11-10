module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_653 : kvxStaticRange 653 17 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_670 : kvxStaticRange 670 18 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
