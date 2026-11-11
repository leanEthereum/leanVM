module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1448 : kvsStaticRange 1448 15 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1463 : kvsStaticRange 1463 16 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
