module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_782 : kwosStaticRange 782 14 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_796 : kwosStaticRange 796 14 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
