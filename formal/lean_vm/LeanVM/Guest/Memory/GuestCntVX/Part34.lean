module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_987 : kvxStaticRange 987 15 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1002 : kvxStaticRange 1002 13 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
