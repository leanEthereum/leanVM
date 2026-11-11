module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1502 : wStaticRange 1502 12 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1514 : wStaticRange 1514 16 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
