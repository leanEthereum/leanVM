module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1016 : kvsStaticRange 1016 9 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1025 : kvsStaticRange 1025 8 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1033 : kvsStaticRange 1033 4 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
