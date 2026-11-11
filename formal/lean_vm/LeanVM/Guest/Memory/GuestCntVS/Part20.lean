module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1433 : kvsStaticRange 1433 8 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1441 : kvsStaticRange 1441 11 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
