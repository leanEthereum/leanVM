module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_662 : wStaticRange 662 16 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_678 : wStaticRange 678 17 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
