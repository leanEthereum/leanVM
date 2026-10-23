module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_634 : kwodStaticRange 634 15 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_649 : kwodStaticRange 649 15 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
