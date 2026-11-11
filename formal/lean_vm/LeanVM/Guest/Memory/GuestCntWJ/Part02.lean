module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_320 : kujStaticRange 320 18 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_338 : kujStaticRange 338 3 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
