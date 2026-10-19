module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_1018 : kwojStaticRange 1018 10 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_1028 : kwojStaticRange 1028 10 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_1038 : kwojStaticRange 1038 5 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
