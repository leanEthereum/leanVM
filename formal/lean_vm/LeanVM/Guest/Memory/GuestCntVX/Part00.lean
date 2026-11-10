module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_0 : kvxStaticRange 0 11 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_11 : kvxStaticRange 11 7 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
