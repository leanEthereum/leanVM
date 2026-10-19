module

public import LeanVM.Guest.Memory.GuestFresh.Temps16

namespace LeanVM.Guest

open Core Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem fresh16_0 : RangeFresh ((Data.core16.body.drop 0).take 182) [164, 165, 1600, 1601, 2972, 2973, 4344, 4345, 5716, 5717, 7088, 7089] temps16 := by
  unfold RangeFresh; decide +kernel

set_option maxRecDepth 100000 in
theorem fresh16_182 : RangeFresh ((Data.core16.body.drop 182).take 24) [8460, 8461, 9832, 9833, 11204, 11205, 12576, 12577, 13948, 13949, 15320, 15321] temps16 := by
  unfold RangeFresh; decide +kernel

end
end LeanVM.Guest
