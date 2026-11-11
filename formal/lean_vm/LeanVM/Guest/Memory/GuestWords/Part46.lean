module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_658 : wStaticRange 658 14 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_672 : wStaticRange 672 17 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
