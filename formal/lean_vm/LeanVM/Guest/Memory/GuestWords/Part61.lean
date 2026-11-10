module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_993 : wStaticRange 993 16 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1009 : wStaticRange 1009 11 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
