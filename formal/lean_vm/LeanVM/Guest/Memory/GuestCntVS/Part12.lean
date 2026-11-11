module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1201 : kvsStaticRange 1201 11 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1212 : kvsStaticRange 1212 15 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
