module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_991 : kvxStaticRange 991 14 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1005 : kvxStaticRange 1005 13 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
