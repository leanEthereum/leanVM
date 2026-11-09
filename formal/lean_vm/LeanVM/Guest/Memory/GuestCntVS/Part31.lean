module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_972 : kvsStaticRange 972 9 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_981 : kvsStaticRange 981 7 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_988 : kvsStaticRange 988 3 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
