module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_739 : wStaticRange 739 18 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_757 : wStaticRange 757 19 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
