module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_590 : wStaticRange 590 19 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_609 : wStaticRange 609 19 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
