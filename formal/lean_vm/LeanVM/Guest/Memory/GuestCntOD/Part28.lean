module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_974 : kwodStaticRange 974 11 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_985 : kwodStaticRange 985 11 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
