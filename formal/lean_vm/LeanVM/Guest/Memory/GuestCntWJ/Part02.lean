module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_293 : kujStaticRange 293 20 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_313 : kujStaticRange 313 3 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
