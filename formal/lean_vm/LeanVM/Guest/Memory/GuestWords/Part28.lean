module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1530 : wStaticRange 1530 13 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1543 : wStaticRange 1543 13 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
