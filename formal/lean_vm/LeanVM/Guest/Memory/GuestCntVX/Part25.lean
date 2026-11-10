module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_649 : kvxStaticRange 649 17 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_666 : kvxStaticRange 666 17 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
