module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1047 : kvsStaticRange 1047 7 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1054 : kvsStaticRange 1054 1 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
