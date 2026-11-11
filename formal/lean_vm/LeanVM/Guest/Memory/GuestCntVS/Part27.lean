module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_813 : kvsStaticRange 813 17 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_830 : kvsStaticRange 830 16 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
