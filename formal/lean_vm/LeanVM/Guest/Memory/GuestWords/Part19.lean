module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1288 : wStaticRange 1288 12 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1300 : wStaticRange 1300 11 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
