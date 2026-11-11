module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_953 : wStaticRange 953 12 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_965 : wStaticRange 965 14 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
