module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_343 : kujStaticRange 343 6 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_349 : kujStaticRange 349 6 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
