module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_677 : kvsStaticRange 677 18 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_695 : kvsStaticRange 695 16 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
