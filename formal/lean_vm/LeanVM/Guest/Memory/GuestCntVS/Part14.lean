module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1735 : kvsStaticRange 1735 12 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1747 : kvsStaticRange 1747 12 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
