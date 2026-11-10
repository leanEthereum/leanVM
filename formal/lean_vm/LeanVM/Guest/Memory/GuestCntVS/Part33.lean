module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_961 : kvsStaticRange 961 14 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_975 : kvsStaticRange 975 12 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
