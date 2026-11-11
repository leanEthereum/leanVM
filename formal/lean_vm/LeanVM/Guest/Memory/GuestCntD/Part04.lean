module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdstaticRange_337 : kwdStaticRange 337 7 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_344 : kwdStaticRange 344 6 := by
  unfold kwdStaticRange; decide +kernel

end
end LeanVM.Guest
