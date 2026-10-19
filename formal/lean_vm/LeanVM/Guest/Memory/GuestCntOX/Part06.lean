module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_181 : kwoxStaticRange 181 1 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_182 : kwoxStaticRange 182 1 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_183 : kwoxStaticRange 183 1 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
