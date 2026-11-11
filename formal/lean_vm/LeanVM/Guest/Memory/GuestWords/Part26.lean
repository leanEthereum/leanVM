module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1483 : wStaticRange 1483 8 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1491 : wStaticRange 1491 11 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
