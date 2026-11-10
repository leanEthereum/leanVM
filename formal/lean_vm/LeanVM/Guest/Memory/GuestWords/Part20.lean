module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1729 : wStaticRange 1729 14 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1743 : wStaticRange 1743 12 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
