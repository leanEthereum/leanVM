module

public import LeanVM.Guest.Memory.GuestMainFree.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem mainFreeRange_255 : MainFreeRange 255 71 := by
  unfold MainFreeRange; decide +kernel

end
end LeanVM.Guest
