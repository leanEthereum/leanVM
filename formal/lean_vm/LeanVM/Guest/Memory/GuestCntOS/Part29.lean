module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_996 : kwosStaticRange 996 11 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_1007 : kwosStaticRange 1007 11 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
