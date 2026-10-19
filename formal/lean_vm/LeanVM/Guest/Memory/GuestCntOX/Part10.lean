module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_195 : kwoxStaticRange 195 1 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_196 : kwoxStaticRange 196 1 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_197 : kwoxStaticRange 197 1 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
