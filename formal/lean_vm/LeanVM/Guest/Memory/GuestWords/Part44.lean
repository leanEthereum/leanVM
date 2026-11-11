module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_587 : wStaticRange 587 19 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_606 : wStaticRange 606 17 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
