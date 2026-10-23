module

public import LeanVM.Guest.Memory.GuestFresh.Temps17

namespace LeanVM.Guest

open Core Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem fresh17_793 : RangeFresh ((Data.core17.body.drop 793).take 16) [34224, 34225, 36172, 36173, 38120, 38121, 40068, 40069] temps17 := by
  unfold RangeFresh; decide +kernel

set_option maxRecDepth 100000 in
theorem fresh17_809 : RangeFresh ((Data.core17.body.drop 809).take 318) [42016, 42017, 43964, 43965, 45912, 45913] temps17 := by
  unfold RangeFresh; decide +kernel

end
end LeanVM.Guest
