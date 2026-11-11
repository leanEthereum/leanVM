module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1119 : kvxStaticRange 1119 14 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1133 : kvxStaticRange 1133 18 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
