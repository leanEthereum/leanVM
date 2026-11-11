module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1485 : wStaticRange 1485 13 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1498 : wStaticRange 1498 12 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
