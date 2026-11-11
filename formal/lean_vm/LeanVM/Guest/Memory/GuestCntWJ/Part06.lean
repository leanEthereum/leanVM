module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_987 : kujStaticRange 987 30 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_1017 : kujStaticRange 1017 20 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
