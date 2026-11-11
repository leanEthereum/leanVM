module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_980 : kvxStaticRange 980 13 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_993 : kvxStaticRange 993 11 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1004 : kvxStaticRange 1004 12 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
