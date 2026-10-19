module

public import LeanVM.Guest.Memory.GuestFresh.Temps16

namespace LeanVM.Guest

open Core Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem fresh16_466 : RangeFresh ((Data.core16.body.drop 466).take 24) [32129, 32130, 33501, 33502, 34873, 34874, 36245, 36246, 37617, 37618, 38989, 38990] temps16 := by
  unfold RangeFresh; decide +kernel

set_option maxRecDepth 100000 in
theorem fresh16_490 : RangeFresh ((Data.core16.body.drop 490).take 24) [40361, 40362, 41733, 41734, 43105, 43106, 44477, 44478, 45849, 45850, 47221, 47222] temps16 := by
  unfold RangeFresh; decide +kernel

end
end LeanVM.Guest
