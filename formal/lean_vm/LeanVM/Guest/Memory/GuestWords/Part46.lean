module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_652 : wStaticRange 652 18 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_670 : wStaticRange 670 17 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
