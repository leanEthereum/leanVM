module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_1018 : kwodStaticRange 1018 10 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_1028 : kwodStaticRange 1028 10 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_1038 : kwodStaticRange 1038 5 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
