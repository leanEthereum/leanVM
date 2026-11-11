module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_725 : wStaticRange 725 16 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_741 : wStaticRange 741 18 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
