module

public import LeanVM.Guest.Memory.GuestCntWX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kuxstaticRange_987 : kuxStaticRange 987 30 := by
  unfold kuxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kuxstaticRange_1017 : kuxStaticRange 1017 20 := by
  unfold kuxStaticRange; decide +kernel

end
end LeanVM.Guest
