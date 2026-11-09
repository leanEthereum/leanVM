module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_661 : kvsStaticRange 661 18 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_679 : kvsStaticRange 679 15 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
