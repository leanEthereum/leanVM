module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1671 : wStaticRange 1671 14 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1685 : wStaticRange 1685 14 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
