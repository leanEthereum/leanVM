module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_564 : kwosStaticRange 564 22 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_586 : kwosStaticRange 586 16 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
