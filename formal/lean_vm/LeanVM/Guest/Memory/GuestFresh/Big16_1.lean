module

public import LeanVM.Guest.Memory.GuestFresh.Temps16

namespace LeanVM.Guest

open Core Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem fresh16_206 : RangeFresh ((Data.core16.body.drop 206).take 24) [16692, 16693, 18064, 18065, 19436, 19437, 20808, 20809, 22180, 22181, 23552, 23553] temps16 := by
  unfold RangeFresh; decide +kernel

set_option maxRecDepth 100000 in
theorem fresh16_230 : RangeFresh ((Data.core16.body.drop 230).take 236) [24924, 24925, 26296, 26297, 26577, 26578, 28013, 28014, 29385, 29386, 30757, 30758] temps16 := by
  unfold RangeFresh; decide +kernel

end
end LeanVM.Guest
