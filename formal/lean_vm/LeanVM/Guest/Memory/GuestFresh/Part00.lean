module

public import LeanVM.Guest.Memory.GuestFresh.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem freshRange_0 : FreshRange 0 12 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_12 : FreshRange 12 3 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_15 : FreshRange 15 1 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_18 : FreshRange 18 52 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_70 : FreshRange 70 108 := by
  unfold FreshRange; decide +kernel

end
end LeanVM.Guest
