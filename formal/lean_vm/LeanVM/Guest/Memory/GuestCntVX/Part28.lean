module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_883 : kvxStaticRange 883 15 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_898 : kvxStaticRange 898 15 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
