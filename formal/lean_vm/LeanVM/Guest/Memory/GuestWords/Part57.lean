module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_826 : wStaticRange 826 13 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_839 : wStaticRange 839 17 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
