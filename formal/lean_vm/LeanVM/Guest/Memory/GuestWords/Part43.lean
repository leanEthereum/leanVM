module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_547 : wStaticRange 547 17 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_564 : wStaticRange 564 18 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
