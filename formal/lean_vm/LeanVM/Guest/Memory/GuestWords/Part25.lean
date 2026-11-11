module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1452 : wStaticRange 1452 19 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1471 : wStaticRange 1471 12 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
