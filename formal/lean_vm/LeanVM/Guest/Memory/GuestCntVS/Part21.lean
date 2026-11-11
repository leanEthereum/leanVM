module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1452 : kvsStaticRange 1452 19 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1471 : kvsStaticRange 1471 12 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
