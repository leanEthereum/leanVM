module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_628 : wStaticRange 628 16 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_644 : wStaticRange 644 18 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
