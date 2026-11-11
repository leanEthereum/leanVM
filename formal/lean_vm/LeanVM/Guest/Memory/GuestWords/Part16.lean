module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1458 : wStaticRange 1458 13 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1471 : wStaticRange 1471 14 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
