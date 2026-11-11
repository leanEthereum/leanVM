module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1020 : kvsStaticRange 1020 8 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1028 : kvsStaticRange 1028 7 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
