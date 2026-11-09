module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_687 : wStaticRange 687 18 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_705 : wStaticRange 705 17 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
