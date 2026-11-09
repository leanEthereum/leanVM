module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_628 : kvsStaticRange 628 16 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_644 : kvsStaticRange 644 17 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
