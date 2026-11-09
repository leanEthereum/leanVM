module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_592 : kvxStaticRange 592 18 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_610 : kvxStaticRange 610 18 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
