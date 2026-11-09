module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_874 : wStaticRange 874 15 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_889 : wStaticRange 889 16 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
