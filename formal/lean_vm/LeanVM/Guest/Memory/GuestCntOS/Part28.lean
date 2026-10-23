module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_974 : kwosStaticRange 974 11 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_985 : kwosStaticRange 985 11 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
