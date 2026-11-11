module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1343 : kvsStaticRange 1343 11 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1354 : kvsStaticRange 1354 19 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
