module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_939 : kvxStaticRange 939 15 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_954 : kvxStaticRange 954 14 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
