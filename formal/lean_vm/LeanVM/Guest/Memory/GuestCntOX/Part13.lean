module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_264 : kwoxStaticRange 264 30 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_294 : kwoxStaticRange 294 30 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_324 : kwoxStaticRange 324 30 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_354 : kwoxStaticRange 354 30 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_384 : kwoxStaticRange 384 30 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_414 : kwoxStaticRange 414 30 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
