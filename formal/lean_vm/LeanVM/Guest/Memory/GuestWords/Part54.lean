module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_730 : wStaticRange 730 17 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_747 : wStaticRange 747 13 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
