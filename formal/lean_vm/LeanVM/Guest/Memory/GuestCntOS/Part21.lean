module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_754 : kwosStaticRange 754 14 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_768 : kwosStaticRange 768 14 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
