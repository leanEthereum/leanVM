module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_576 : kvxStaticRange 576 19 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_595 : kvxStaticRange 595 18 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
