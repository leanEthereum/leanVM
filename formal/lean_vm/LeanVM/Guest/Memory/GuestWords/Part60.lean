module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_969 : wStaticRange 969 13 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_982 : wStaticRange 982 11 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
