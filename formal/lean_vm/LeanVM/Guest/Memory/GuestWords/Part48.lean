module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_707 : wStaticRange 707 18 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_725 : wStaticRange 725 14 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
