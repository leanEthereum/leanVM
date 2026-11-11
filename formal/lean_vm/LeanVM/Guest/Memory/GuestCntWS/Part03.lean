module

public import LeanVM.Guest.Memory.GuestCntWS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kusstaticRange_344 : kusStaticRange 344 6 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_350 : kusStaticRange 350 7 := by
  unfold kusStaticRange; decide +kernel

end
end LeanVM.Guest
