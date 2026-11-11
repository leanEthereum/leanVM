module

public import LeanVM.Guest.Memory.GuestCntWS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kusstaticRange_343 : kusStaticRange 343 6 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_349 : kusStaticRange 349 6 := by
  unfold kusStaticRange; decide +kernel

end
end LeanVM.Guest
