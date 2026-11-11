module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_954 : kvsStaticRange 954 12 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_966 : kvsStaticRange 966 14 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
