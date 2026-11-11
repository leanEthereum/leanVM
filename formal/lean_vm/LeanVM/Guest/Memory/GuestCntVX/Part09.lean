module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1066 : kvxStaticRange 1066 20 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1086 : kvxStaticRange 1086 13 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1099 : kvxStaticRange 1099 20 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
