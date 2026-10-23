module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_1018 : kwoxStaticRange 1018 10 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_1028 : kwoxStaticRange 1028 10 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_1038 : kwoxStaticRange 1038 5 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
