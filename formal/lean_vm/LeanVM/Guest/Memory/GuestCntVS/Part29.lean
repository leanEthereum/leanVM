module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_786 : kvsStaticRange 786 18 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_804 : kvsStaticRange 804 17 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
