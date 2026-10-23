module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_17 : kwosStaticRange 17 1 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
