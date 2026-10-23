module

public import LeanVM.Guest.Memory.GuestMainFree.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem mainFreeRange_726 : MainFreeRange 726 70 := by
  unfold MainFreeRange; decide +kernel

end
end LeanVM.Guest
