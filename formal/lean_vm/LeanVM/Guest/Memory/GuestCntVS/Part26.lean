module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_766 : kvsStaticRange 766 18 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_784 : kvsStaticRange 784 20 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_804 : kvsStaticRange 804 24 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_828 : kvsStaticRange 828 22 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
