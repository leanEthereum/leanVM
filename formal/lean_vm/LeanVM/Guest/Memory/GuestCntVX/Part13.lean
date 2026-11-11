module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1674 : kvxStaticRange 1674 13 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1687 : kvxStaticRange 1687 13 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
