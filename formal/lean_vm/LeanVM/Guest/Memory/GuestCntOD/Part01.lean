module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_14 : kwodStaticRange 14 1 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
