module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_444 : kwoxStaticRange 444 30 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_474 : kwoxStaticRange 474 30 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_504 : kwoxStaticRange 504 30 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_534 : kwoxStaticRange 534 30 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
