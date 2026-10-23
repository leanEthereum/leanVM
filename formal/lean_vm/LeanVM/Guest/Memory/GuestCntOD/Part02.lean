module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_15 : kwodStaticRange 15 2 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
