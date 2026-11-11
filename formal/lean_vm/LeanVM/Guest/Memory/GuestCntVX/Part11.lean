module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1448 : kvxStaticRange 1448 15 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1463 : kvxStaticRange 1463 16 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
