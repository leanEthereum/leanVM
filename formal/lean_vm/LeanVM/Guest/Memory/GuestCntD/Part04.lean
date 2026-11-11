module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdstaticRange_336 : kwdStaticRange 336 6 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_342 : kwdStaticRange 342 6 := by
  unfold kwdStaticRange; decide +kernel

end
end LeanVM.Guest
