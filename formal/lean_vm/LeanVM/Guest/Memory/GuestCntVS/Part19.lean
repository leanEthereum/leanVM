module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1397 : kvsStaticRange 1397 18 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1415 : kvsStaticRange 1415 18 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
