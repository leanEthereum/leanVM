module

public import LeanVM.Guest.Memory.GuestCntWS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kusstaticRange_320 : kusStaticRange 320 18 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_338 : kusStaticRange 338 3 := by
  unfold kusStaticRange; decide +kernel

end
end LeanVM.Guest
