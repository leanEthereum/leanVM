module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1502 : kvxStaticRange 1502 12 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1514 : kvxStaticRange 1514 16 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
