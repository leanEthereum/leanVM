module

public import LeanVM.Guest.Memory.GuestCntWS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kusstaticRange_342 : kusStaticRange 342 6 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_348 : kusStaticRange 348 6 := by
  unfold kusStaticRange; decide +kernel

end
end LeanVM.Guest
