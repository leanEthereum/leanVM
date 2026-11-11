module

public import LeanVM.Guest.Memory.GuestCntWS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kusstaticRange_987 : kusStaticRange 987 30 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_1017 : kusStaticRange 1017 20 := by
  unfold kusStaticRange; decide +kernel

end
end LeanVM.Guest
