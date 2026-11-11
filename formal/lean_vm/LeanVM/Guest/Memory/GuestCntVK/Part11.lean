module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1151 : kvkStaticRange 1151 18 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1169 : kvkStaticRange 1169 12 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1181 : kvkStaticRange 1181 20 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
