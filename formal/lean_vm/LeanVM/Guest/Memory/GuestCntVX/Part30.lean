module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_959 : kvxStaticRange 959 13 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_972 : kvxStaticRange 972 14 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
