module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_677 : kvxStaticRange 677 18 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_695 : kvxStaticRange 695 16 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
