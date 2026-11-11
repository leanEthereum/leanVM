module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1503 : kvsStaticRange 1503 12 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1515 : kvsStaticRange 1515 10 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
