module

public import LeanVM.Guest.Memory.GuestFresh.Temps16

namespace LeanVM.Guest

open Core Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem fresh16_514 : RangeFresh ((Data.core16.body.drop 514).take 216) [48593, 48594, 49965, 49966, 51337, 51338, 52709, 52710] temps16 := by
  unfold RangeFresh; decide +kernel

end
end LeanVM.Guest
