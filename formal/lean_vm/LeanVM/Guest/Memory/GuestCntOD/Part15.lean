module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_564 : kwodStaticRange 564 22 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_586 : kwodStaticRange 586 16 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
