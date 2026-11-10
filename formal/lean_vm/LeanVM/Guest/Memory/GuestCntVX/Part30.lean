module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_815 : kvxStaticRange 815 16 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_831 : kvxStaticRange 831 17 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
