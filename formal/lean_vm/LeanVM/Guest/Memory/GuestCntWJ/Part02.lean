module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_320 : kujStaticRange 320 16 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_336 : kujStaticRange 336 6 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
