module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_320 : kujStaticRange 320 17 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_337 : kujStaticRange 337 7 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
