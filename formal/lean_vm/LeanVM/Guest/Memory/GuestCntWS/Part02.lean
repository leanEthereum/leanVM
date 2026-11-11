module

public import LeanVM.Guest.Memory.GuestCntWS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kusstaticRange_288 : kusStaticRange 288 25 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_313 : kusStaticRange 313 3 := by
  unfold kusStaticRange; decide +kernel

end
end LeanVM.Guest
