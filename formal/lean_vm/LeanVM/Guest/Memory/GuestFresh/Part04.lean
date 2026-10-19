module

public import LeanVM.Guest.Memory.GuestFresh.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem freshRange_688 : FreshRange 688 150 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_838 : FreshRange 838 139 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_977 : FreshRange 977 15 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_992 : FreshRange 992 17 := by
  unfold FreshRange; decide +kernel

end
end LeanVM.Guest
