module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1699 : wStaticRange 1699 11 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1710 : wStaticRange 1710 12 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
