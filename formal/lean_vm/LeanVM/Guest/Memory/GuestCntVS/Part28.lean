module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_755 : kvsStaticRange 755 14 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_769 : kvsStaticRange 769 17 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
