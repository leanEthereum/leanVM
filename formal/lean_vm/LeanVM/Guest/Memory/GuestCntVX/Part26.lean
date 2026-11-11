module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_779 : kvxStaticRange 779 18 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_797 : kvxStaticRange 797 16 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
