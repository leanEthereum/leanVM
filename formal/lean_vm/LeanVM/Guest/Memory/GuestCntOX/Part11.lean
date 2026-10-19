module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_198 : kwoxStaticRange 198 2 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_200 : kwoxStaticRange 200 1 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_201 : kwoxStaticRange 201 1 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
