module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_291 : kujStaticRange 291 18 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_309 : kujStaticRange 309 7 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
