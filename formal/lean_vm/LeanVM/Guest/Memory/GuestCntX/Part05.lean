module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_321 : kwxStaticRange 321 7 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_328 : kwxStaticRange 328 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_358 : kwxStaticRange 358 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_388 : kwxStaticRange 388 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_418 : kwxStaticRange 418 30 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
