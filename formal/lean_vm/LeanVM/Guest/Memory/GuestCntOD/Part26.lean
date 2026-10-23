module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_894 : kwodStaticRange 894 14 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_908 : kwodStaticRange 908 17 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
