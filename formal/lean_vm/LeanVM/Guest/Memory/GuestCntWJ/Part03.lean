module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_344 : kujStaticRange 344 6 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_350 : kujStaticRange 350 7 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
