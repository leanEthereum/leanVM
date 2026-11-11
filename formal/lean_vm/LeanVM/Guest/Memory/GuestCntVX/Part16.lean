module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1311 : kvxStaticRange 1311 20 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1331 : kvxStaticRange 1331 12 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
