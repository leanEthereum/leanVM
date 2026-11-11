module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1433 : wStaticRange 1433 8 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1441 : wStaticRange 1441 11 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
