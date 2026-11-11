module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1256 : wStaticRange 1256 12 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1268 : wStaticRange 1268 20 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
