module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_1073 : wStaticRange 1073 18 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_1091 : wStaticRange 1091 18 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
