module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_959 : kvsStaticRange 959 13 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_972 : kvsStaticRange 972 14 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
