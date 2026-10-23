module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_810 : kwosStaticRange 810 14 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_824 : kwosStaticRange 824 14 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
