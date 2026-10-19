module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_925 : kwosStaticRange 925 28 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_953 : kwosStaticRange 953 21 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
