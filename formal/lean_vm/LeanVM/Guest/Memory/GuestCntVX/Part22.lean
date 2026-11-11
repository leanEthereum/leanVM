module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_644 : kvxStaticRange 644 16 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_660 : kvxStaticRange 660 17 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
