module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1343 : wStaticRange 1343 11 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1354 : wStaticRange 1354 19 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
