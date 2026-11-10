module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1777 : wStaticRange 1777 11 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1788 : wStaticRange 1788 10 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1798 : wStaticRange 1798 5 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
