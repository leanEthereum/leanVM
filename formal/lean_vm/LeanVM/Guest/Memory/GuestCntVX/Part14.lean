module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1525 : kvxStaticRange 1525 10 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
