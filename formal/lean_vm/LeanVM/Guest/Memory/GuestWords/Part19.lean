module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1700 : wStaticRange 1700 14 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1714 : wStaticRange 1714 15 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
