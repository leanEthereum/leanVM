module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1311 : wStaticRange 1311 20 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1331 : wStaticRange 1331 12 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
