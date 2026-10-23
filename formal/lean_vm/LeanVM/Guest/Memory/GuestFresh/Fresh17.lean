module

public import LeanVM.Guest.Memory.GuestFresh.Big17_0
public import LeanVM.Guest.Memory.GuestFresh.Big17_1
public import LeanVM.Guest.Memory.GuestFresh.Big17_2

namespace LeanVM.Guest

open Core Memory

@[expose] public section

set_option maxRecDepth 100000 in
/-- Function 17's temporaries are fresh, by ranges of its statements. -/
theorem core17_fresh : Data.core17.Fresh := by
  have h1127 : RangeFresh (Data.core17.body.drop 1127) [] temps17 :=
    rangeFresh_end (by decide +kernel) temps17
  have h809 : RangeFresh (Data.core17.body.drop 809) [42016, 42017, 43964, 43965, 45912, 45913] temps17 :=
    rangeFresh_drop fresh17_809 h1127
  have h793 : RangeFresh (Data.core17.body.drop 793) [34224, 34225, 36172, 36173, 38120, 38121, 40068, 40069, 42016, 42017, 43964, 43965, 45912, 45913] temps17 :=
    rangeFresh_drop fresh17_793 h809
  have h777 : RangeFresh (Data.core17.body.drop 777) [26432, 26433, 28380, 28381, 30328, 30329, 32276, 32277, 34224, 34225, 36172, 36173, 38120, 38121, 40068, 40069, 42016, 42017, 43964, 43965, 45912, 45913] temps17 :=
    rangeFresh_drop fresh17_777 h793
  have h761 : RangeFresh (Data.core17.body.drop 761) [18640, 18641, 20588, 20589, 22536, 22537, 24484, 24485, 26432, 26433, 28380, 28381, 30328, 30329, 32276, 32277, 34224, 34225, 36172, 36173, 38120, 38121, 40068, 40069, 42016, 42017, 43964, 43965, 45912, 45913] temps17 :=
    rangeFresh_drop fresh17_761 h777
  have h745 : RangeFresh (Data.core17.body.drop 745) [10848, 10849, 12796, 12797, 14744, 14745, 16692, 16693, 18640, 18641, 20588, 20589, 22536, 22537, 24484, 24485, 26432, 26433, 28380, 28381, 30328, 30329, 32276, 32277, 34224, 34225, 36172, 36173, 38120, 38121, 40068, 40069, 42016, 42017, 43964, 43965, 45912, 45913] temps17 :=
    rangeFresh_drop fresh17_745 h761
  have h0 : RangeFresh (Data.core17.body.drop 0) [214, 215, 221, 222, 226, 227, 339, 340, 344, 345, 779, 780, 786, 787, 791, 792, 904, 905, 909, 910, 1344, 1345, 1351, 1352, 1356, 1357, 1469, 1470, 1474, 1475, 1909, 1910, 1916, 1917, 1921, 1922, 2034, 2035, 2039, 2040, 2474, 2475, 2481, 2482, 2486, 2487, 2599, 2600, 2604, 2605, 3039, 3040, 3046, 3047, 3051, 3052, 3164, 3165, 3169, 3170, 3604, 3605, 3611, 3612, 3616, 3617, 3729, 3730, 3734, 3735, 4169, 4170, 4176, 4177, 4181, 4182, 4294, 4295, 4299, 4300, 4940, 4941, 6952, 6953, 8900, 8901, 10848, 10849, 12796, 12797, 14744, 14745, 16692, 16693, 18640, 18641, 20588, 20589, 22536, 22537, 24484, 24485, 26432, 26433, 28380, 28381, 30328, 30329, 32276, 32277, 34224, 34225, 36172, 36173, 38120, 38121, 40068, 40069, 42016, 42017, 43964, 43965, 45912, 45913] temps17 :=
    rangeFresh_drop fresh17_0 h745
  exact fn_fresh_of_rangeFresh h0 (by decide +kernel) (by decide +kernel)

end
end LeanVM.Guest
