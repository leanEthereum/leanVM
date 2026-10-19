module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_634 : kwosStaticRange 634 15 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_649 : kwosStaticRange 649 15 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
