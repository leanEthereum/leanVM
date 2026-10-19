module

public import LeanVM.Guest.Memory.GuestFresh.Range

namespace LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem freshRange_194 : FreshRange 194 4 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_198 : FreshRange 198 5 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_203 : FreshRange 203 107 := by
  unfold FreshRange; decide +kernel

set_option maxRecDepth 100000 in
theorem freshRange_310 : FreshRange 310 150 := by
  unfold FreshRange; decide +kernel

end
end LeanVM.Guest
