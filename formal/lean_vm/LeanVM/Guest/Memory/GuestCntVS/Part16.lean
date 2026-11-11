module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1311 : kvsStaticRange 1311 20 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1331 : kvsStaticRange 1331 12 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
