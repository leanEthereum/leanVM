module

public import LeanVM.Guest.Memory.GuestFresh.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem freshRange_460 : FreshRange 460 59 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_519 : FreshRange 519 29 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_548 : FreshRange 548 24 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_572 : FreshRange 572 116 := by
  unfold FreshRange; decide +kernel

end
end LeanVM.Guest
