module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_987 : kvsStaticRange 987 15 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1002 : kvsStaticRange 1002 13 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
