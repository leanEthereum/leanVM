module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1755 : wStaticRange 1755 12 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1767 : wStaticRange 1767 10 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
