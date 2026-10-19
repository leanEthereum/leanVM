module

public import LeanVM.Guest.Memory.GuestFresh.Temps17

namespace LeanVM.Guest

open Core Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem fresh17_0 : RangeFresh ((Data.core17.body.drop 0).take 745) [214, 215, 221, 222, 226, 227, 339, 340, 344, 345, 779, 780, 786, 787, 791, 792, 904, 905, 909, 910, 1344, 1345, 1351, 1352, 1356, 1357, 1469, 1470, 1474, 1475, 1909, 1910, 1916, 1917, 1921, 1922, 2034, 2035, 2039, 2040, 2474, 2475, 2481, 2482, 2486, 2487, 2599, 2600, 2604, 2605, 3039, 3040, 3046, 3047, 3051, 3052, 3164, 3165, 3169, 3170, 3604, 3605, 3611, 3612, 3616, 3617, 3729, 3730, 3734, 3735, 4169, 4170, 4176, 4177, 4181, 4182, 4294, 4295, 4299, 4300, 4940, 4941, 6952, 6953, 8900, 8901] temps17 := by
  unfold RangeFresh; decide +kernel

set_option maxRecDepth 100000 in
theorem fresh17_745 : RangeFresh ((Data.core17.body.drop 745).take 16) [10848, 10849, 12796, 12797, 14744, 14745, 16692, 16693] temps17 := by
  unfold RangeFresh; decide +kernel

end
end LeanVM.Guest
