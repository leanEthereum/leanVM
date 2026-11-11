module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1016 : wStaticRange 1016 9 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1025 : wStaticRange 1025 8 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1033 : wStaticRange 1033 4 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
