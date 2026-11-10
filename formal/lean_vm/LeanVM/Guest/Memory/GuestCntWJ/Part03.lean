module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_342 : kujStaticRange 342 6 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_348 : kujStaticRange 348 6 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
