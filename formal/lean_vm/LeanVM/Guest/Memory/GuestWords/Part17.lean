module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1223 : wStaticRange 1223 18 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1241 : wStaticRange 1241 15 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
