module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_930 : wStaticRange 930 13 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_943 : wStaticRange 943 15 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
