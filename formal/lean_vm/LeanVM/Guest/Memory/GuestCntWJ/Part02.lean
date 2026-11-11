module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_289 : kujStaticRange 289 20 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_309 : kujStaticRange 309 3 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
