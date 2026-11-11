module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1502 : kvsStaticRange 1502 12 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1514 : kvsStaticRange 1514 16 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
