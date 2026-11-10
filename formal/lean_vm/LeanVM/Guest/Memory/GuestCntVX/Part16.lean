module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1782 : kvxStaticRange 1782 11 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1793 : kvxStaticRange 1793 10 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
