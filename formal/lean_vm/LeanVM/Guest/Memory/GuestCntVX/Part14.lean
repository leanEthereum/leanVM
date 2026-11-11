module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1257 : kvxStaticRange 1257 14 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1271 : kvxStaticRange 1271 21 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
