module

public import LeanVM.Guest.Memory.GuestFresh.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem freshRange_1009 : FreshRange 1009 15 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_1024 : FreshRange 1024 14 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_1038 : FreshRange 1038 5 := by
  unfold FreshRange; decide +kernel

end
end LeanVM.Guest
