module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_350 : kwxStaticRange 350 7 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_357 : kwxStaticRange 357 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_387 : kwxStaticRange 387 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_417 : kwxStaticRange 417 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_447 : kwxStaticRange 447 30 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
