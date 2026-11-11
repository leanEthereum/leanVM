module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1556 : wStaticRange 1556 13 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1569 : wStaticRange 1569 12 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
