module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_688 : kvxStaticRange 688 14 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_702 : kvxStaticRange 702 19 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
