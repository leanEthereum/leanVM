module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_345 : kvsStaticRange 345 2 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_347 : kvsStaticRange 347 1 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
