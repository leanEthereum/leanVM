module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_940 : wStaticRange 940 15 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_955 : wStaticRange 955 14 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
