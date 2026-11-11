module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1645 : kvxStaticRange 1645 16 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1661 : kvxStaticRange 1661 13 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
