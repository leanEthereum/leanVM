module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_718 : kvxStaticRange 718 13 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_731 : kvxStaticRange 731 17 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
