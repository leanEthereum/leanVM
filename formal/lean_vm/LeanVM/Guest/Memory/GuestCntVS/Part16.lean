module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1782 : kvsStaticRange 1782 11 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1793 : kvsStaticRange 1793 10 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
