module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_582 : wStaticRange 582 19 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_601 : wStaticRange 601 15 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
