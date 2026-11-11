module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_790 : wStaticRange 790 18 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_808 : wStaticRange 808 13 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
