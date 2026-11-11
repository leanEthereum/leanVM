module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1227 : kvsStaticRange 1227 19 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1246 : kvsStaticRange 1246 11 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
