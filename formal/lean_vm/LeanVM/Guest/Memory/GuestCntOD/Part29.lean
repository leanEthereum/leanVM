module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_996 : kwodStaticRange 996 11 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_1007 : kwodStaticRange 1007 11 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
