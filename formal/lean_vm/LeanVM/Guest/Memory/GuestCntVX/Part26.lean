module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_778 : kvxStaticRange 778 12 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_790 : kvxStaticRange 790 18 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
