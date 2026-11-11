module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1581 : wStaticRange 1581 12 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1593 : wStaticRange 1593 8 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
