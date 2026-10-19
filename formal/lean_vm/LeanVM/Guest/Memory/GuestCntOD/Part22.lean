module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_782 : kwodStaticRange 782 14 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_796 : kwodStaticRange 796 14 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
