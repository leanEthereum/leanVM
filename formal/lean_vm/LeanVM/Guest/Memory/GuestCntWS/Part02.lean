module

public import LeanVM.Guest.Memory.GuestCntWS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kusstaticRange_320 : kusStaticRange 320 17 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_337 : kusStaticRange 337 7 := by
  unfold kusStaticRange; decide +kernel

end
end LeanVM.Guest
