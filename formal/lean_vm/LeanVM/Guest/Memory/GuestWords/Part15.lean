module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1162 : wStaticRange 1162 11 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1173 : wStaticRange 1173 18 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
