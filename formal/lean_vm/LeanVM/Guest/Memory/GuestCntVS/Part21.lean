module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_612 : kvsStaticRange 612 14 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_626 : kvsStaticRange 626 18 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
