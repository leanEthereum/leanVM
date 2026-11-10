module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1015 : kvsStaticRange 1015 10 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1025 : kvsStaticRange 1025 13 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1038 : kvsStaticRange 1038 9 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
