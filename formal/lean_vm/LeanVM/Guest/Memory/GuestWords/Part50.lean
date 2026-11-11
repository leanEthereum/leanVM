module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_776 : wStaticRange 776 13 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_789 : wStaticRange 789 18 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
