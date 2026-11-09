module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_730 : kvxStaticRange 730 18 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_748 : kvxStaticRange 748 18 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
