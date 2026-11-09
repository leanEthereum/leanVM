module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_722 : wStaticRange 722 18 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_740 : wStaticRange 740 18 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
