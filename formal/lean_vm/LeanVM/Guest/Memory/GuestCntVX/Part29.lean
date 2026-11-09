module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_913 : kvxStaticRange 913 12 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_925 : kvxStaticRange 925 11 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
