module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_664 : kwosStaticRange 664 15 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_679 : kwosStaticRange 679 15 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
