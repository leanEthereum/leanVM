module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1373 : wStaticRange 1373 14 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1387 : wStaticRange 1387 10 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
