module

public import LeanVM.Guest.Memory.GuestCntWS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kusstaticRange_316 : kusStaticRange 316 3 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_319 : kusStaticRange 319 2 := by
  unfold kusStaticRange; decide +kernel

end
end LeanVM.Guest
