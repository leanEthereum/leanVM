module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_815 : kvsStaticRange 815 16 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_831 : kvsStaticRange 831 17 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
