module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_556 : kvsStaticRange 556 18 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_574 : kvsStaticRange 574 18 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
