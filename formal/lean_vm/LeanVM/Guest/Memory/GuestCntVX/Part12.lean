module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1201 : kvxStaticRange 1201 11 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1212 : kvxStaticRange 1212 15 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
