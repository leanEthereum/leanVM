module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_939 : kvkStaticRange 939 15 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_954 : kvkStaticRange 954 14 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
