module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_759 : wStaticRange 759 19 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_778 : wStaticRange 778 12 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
