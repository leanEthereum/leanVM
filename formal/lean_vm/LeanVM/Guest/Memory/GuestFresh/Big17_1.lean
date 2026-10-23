module

public import LeanVM.Guest.Memory.GuestFresh.Temps17

namespace LeanVM.Guest

open Core Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem fresh17_761 : RangeFresh ((Data.core17.body.drop 761).take 16) [18640, 18641, 20588, 20589, 22536, 22537, 24484, 24485] temps17 := by
  unfold RangeFresh; decide +kernel

set_option maxRecDepth 100000 in
theorem fresh17_777 : RangeFresh ((Data.core17.body.drop 777).take 16) [26432, 26433, 28380, 28381, 30328, 30329, 32276, 32277] temps17 := by
  unfold RangeFresh; decide +kernel

end
end LeanVM.Guest
