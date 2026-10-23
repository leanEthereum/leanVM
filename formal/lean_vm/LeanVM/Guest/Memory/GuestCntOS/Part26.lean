module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_894 : kwosStaticRange 894 14 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_908 : kwosStaticRange 908 17 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
