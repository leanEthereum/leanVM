module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_664 : kwodStaticRange 664 15 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_679 : kwodStaticRange 679 15 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
