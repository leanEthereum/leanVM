module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_972 : kvxStaticRange 972 9 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_981 : kvxStaticRange 981 7 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_988 : kvxStaticRange 988 3 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
