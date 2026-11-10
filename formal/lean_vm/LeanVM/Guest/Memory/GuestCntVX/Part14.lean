module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1735 : kvxStaticRange 1735 12 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1747 : kvxStaticRange 1747 12 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
