module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_307 : kwxStaticRange 307 7 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_314 : kwxStaticRange 314 7 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
