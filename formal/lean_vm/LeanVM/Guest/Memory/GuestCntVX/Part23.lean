module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_661 : kvxStaticRange 661 18 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_679 : kvxStaticRange 679 15 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
