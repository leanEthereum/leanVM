module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_883 : kvsStaticRange 883 15 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_898 : kvsStaticRange 898 15 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
