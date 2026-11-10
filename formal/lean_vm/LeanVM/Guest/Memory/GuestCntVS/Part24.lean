module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_613 : kvsStaticRange 613 19 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_632 : kvsStaticRange 632 17 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
