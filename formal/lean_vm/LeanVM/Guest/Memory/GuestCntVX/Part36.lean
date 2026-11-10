module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1047 : kvxStaticRange 1047 7 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1054 : kvxStaticRange 1054 1 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
