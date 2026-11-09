module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_905 : wStaticRange 905 15 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_920 : wStaticRange 920 10 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
