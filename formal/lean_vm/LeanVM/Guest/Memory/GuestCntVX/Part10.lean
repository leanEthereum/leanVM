module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_345 : kvxStaticRange 345 2 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_347 : kvxStaticRange 347 1 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
