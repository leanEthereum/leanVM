module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_316 : kujStaticRange 316 3 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_319 : kujStaticRange 319 2 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
