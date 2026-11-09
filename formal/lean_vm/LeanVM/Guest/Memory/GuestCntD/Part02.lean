module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdstaticRange_36 : kwdStaticRange 36 1 := by
  unfold kwdStaticRange; decide +kernel

end
end LeanVM.Guest
