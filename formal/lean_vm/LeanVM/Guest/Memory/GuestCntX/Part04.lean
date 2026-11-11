module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_337 : kwxStaticRange 337 3 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_340 : kwxStaticRange 340 3 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
