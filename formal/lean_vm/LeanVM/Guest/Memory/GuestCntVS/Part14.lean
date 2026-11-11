module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1257 : kvsStaticRange 1257 14 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1271 : kvsStaticRange 1271 21 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
