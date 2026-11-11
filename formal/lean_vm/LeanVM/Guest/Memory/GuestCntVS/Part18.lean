module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1373 : kvsStaticRange 1373 14 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1387 : kvsStaticRange 1387 10 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
