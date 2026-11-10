module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_618 : kvsStaticRange 618 18 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_636 : kvsStaticRange 636 17 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
